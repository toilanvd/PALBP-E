#include <bits/stdc++.h>
#include <thread>
#include <mutex>
#include <atomic>

using namespace std;

const double eps = 1e-9;
const int INF = 1e9;

const int MAXN = 100;
const int MAXWSTSIZE = 3;

const int ITERATION_LIMIT = -1; // = -1 for a full search
const int PRINT_INTERVAL  = 1; // In kết quả sau mỗi N solution được sinh ra
atomic<int> iterationCnt;

// ─── Input data (read-only after readInput) ───────────────────────────────────

struct task {
    string machine;
    string machine_name;
    int type;
    double worktime;
    int status;
    int level;
    vector<int> edge, originEdge;
    vector<int> revEdge;
};

struct edge_reserve {
    vector<int> edge, originEdge;
    vector<int> revEdge;
};

int N, NConst;
double Delta;
task taskList[MAXN + 5];
edge_reserve edge_rs[MAXN + 5];

// ─── Thread-local task state ──────────────────────────────────────────────────

struct LocalTask {
    int status;
    vector<int> edge, originEdge, revEdge;
};

using LocalTaskArr = array<LocalTask, MAXN + 5>;

LocalTaskArr makeLocalTasks() {
    LocalTaskArr lt;
    for (int i = 1; i <= N; i++) {
        lt[i].status     = taskList[i].status;
        lt[i].edge       = taskList[i].edge;
        lt[i].originEdge = taskList[i].originEdge;
        lt[i].revEdge    = taskList[i].revEdge;
    }
    return lt;
}

// ─── Solution ─────────────────────────────────────────────────────────────────

struct solution {
    int workers;
    vector<vector<int>> workstations;
    double R;
    double SI;
};

solution finalRes;
mutex finalRes_mutex;
mutex print_mutex;

// bestSI chia sẻ giữa các thread để pruning.
// SI = M*R² - 2R*ΣRj + ΣRj² (không chia M) nên đơn điệu không giảm
// khi thêm workstation → pruning hợp lệ.
double bestSI = 1e18;
mutex bestSI_mutex;

void readInput() {
    //freopen("Test/Scholl-tests/Sawyer-0.txt", "r", stdin);

    cin >> N >> NConst >> Delta;
    Delta /= 100.0;
    for (int i = 1; i <= N; i++) {
        int ign;
        cin >> ign >> taskList[i].machine >> taskList[i].type
            >> taskList[i].worktime >> taskList[i].level;
        taskList[i].status = 1;
    }
    int M; cin >> M;
    while (M--) {
        int u, v; cin >> u >> v;
        taskList[u].edge.push_back(v);       taskList[u].originEdge.push_back(v);
        taskList[v].revEdge.push_back(u);
        edge_rs[u].edge.push_back(v);        edge_rs[u].originEdge.push_back(v);
        edge_rs[v].revEdge.push_back(u);
    }
}

inline double getBestSI() {
    lock_guard<mutex> lk(bestSI_mutex);
    return bestSI;
}

inline void updateBestSI(double val) {
    lock_guard<mutex> lk(bestSI_mutex);
    if (val < bestSI) bestSI = val;
}

bool cmpSolution(const solution& X, const solution& Y); // forward declaration

// Điểm ghi duy nhất vào finalRes — luôn đồng bộ bestSI.
inline void updateFinalRes(const solution& candidate) {
    if (candidate.workers > NConst) return;
    lock_guard<mutex> lk(finalRes_mutex);
    if (cmpSolution(candidate, finalRes)) {
        finalRes = candidate;
        updateBestSI(finalRes.SI);
    }
}

bool cmpSolution(const solution& X, const solution& Y) {
    if (X.workers > NConst) return false;
    if (Y.workers > NConst) return true;
    if (fabs(X.SI - Y.SI) > eps) return X.SI < Y.SI;
    if (fabs(X.R * X.R * (double)X.workstations.size() - Y.R * Y.R * (double)Y.workstations.size()) > eps) return X.R * X.R * (double)X.workstations.size() < Y.R * Y.R * (double)Y.workstations.size();
    return false;
}

// ─── DFS / validation (thread-local) ─────────────────────────────────────────

static bool dfs1_local(int u, int rev,
                       set<int>& reachableTask,
                       const set<int>& workstationElements,
                       LocalTaskArr& lt)
{
    if (rev == -1
        && workstationElements.find(u) == workstationElements.end()
        && reachableTask.find(u) != reachableTask.end())
        return true;

    reachableTask.insert(u * rev);

    if (rev == 1) {
        for (int v : lt[u].edge) {
            if (lt[v].status < 0) v = -lt[v].status;
            if (reachableTask.find(v) == reachableTask.end())
                dfs1_local(v, rev, reachableTask, workstationElements, lt);
        }
    } else {
        for (int v : lt[u].revEdge) {
            if (lt[v].status < 0) v = -lt[v].status;
            if (reachableTask.find(v * rev) == reachableTask.end()
                && dfs1_local(v, rev, reachableTask, workstationElements, lt))
                return true;
        }
    }
    return false;
}

static bool tooLargeOrBadPair(const vector<int>& wst) {
    if ((int)wst.size() > MAXWSTSIZE) return true;
    set<string> machine;
    for (int x : wst) machine.insert(taskList[x].machine);
    if ((int)machine.size() > 2) return true;
    set<int> type;
    for (int x : wst) type.insert(taskList[x].type);
    if ((int)machine.size() == 2) {
        if ((int)type.size() == 1 && type.count(1)) return true;
        if (type.count(1) && type.count(2))          return true;
    }
    return false;
}

static bool validWorkstation_local(const vector<int>& wst, LocalTaskArr& lt) {
    if (tooLargeOrBadPair(wst)) return false;
    set<int> reachableTask, workstationElements;
    for (int x : wst) {
        workstationElements.insert(x);
        dfs1_local(x, 1, reachableTask, workstationElements, lt);
    }
    for (int x : wst)
        if (dfs1_local(x, -1, reachableTask, workstationElements, lt))
            return false;
    return true;
}

// ─── Workstation / solution stats ────────────────────────────────────────────

struct workstationStat {
    int workers, workerSaved, tasks;
    double totalWorktime, Rj;
};

workstationStat calWorkstationStat(const vector<int>& wst, double R) {
    workstationStat stat; stat.totalWorktime = 0;
    int baseWorkers = 0;
    for (int x : wst) {
        stat.totalWorktime += taskList[x].worktime;
        double t = taskList[x].worktime;
        if      (t <= R)   baseWorkers++;
        else if (t <= 2*R) baseWorkers += 2;
        else               baseWorkers += 3;
    }
    if      (stat.totalWorktime <= R   * (1.0 + Delta) + eps) { stat.workers = 1; }
    else if (stat.totalWorktime <= 2*R * (1.0 + Delta) + eps) { stat.workers = 2; }
    else                                                       { stat.workers = 3; }
    stat.workerSaved = baseWorkers - stat.workers;
    stat.Rj   = stat.totalWorktime / stat.workers;
    stat.tasks = (int)wst.size();
    return stat;
}

typedef pair<int,int>   ii;
typedef pair<double,ii> pdii;

bool cmpPdii(const pdii& X, const pdii& Y) {
    if (fabs(X.first - Y.first) > eps) return X.first < Y.first;
    return false;
}

// SI = M*R² - 2R*ΣRj + ΣRj²  (không chia M, khác bản cũ)
void calSolutionStat(solution* sol) {
    vector<workstationStat> wstStats;
    vector<pdii> potentialR;
    (*sol).SI      = INF;
    (*sol).workers = INF;
    (*sol).R       = INF;
    double sumRj = 0, sumSquaredRj = 0;
    int curWorkers = (int)(*sol).workstations.size();

    for (int i = 0; i < (int)(*sol).workstations.size(); i++) {
        wstStats.push_back(calWorkstationStat((*sol).workstations[i], INF));
        sumRj        += wstStats.back().Rj;
        sumSquaredRj += wstStats.back().Rj * wstStats.back().Rj;
        for (int j = 1; j <= 3; j++)
            potentialR.push_back(pdii(
                wstStats.back().totalWorktime / ((double)j * (1.0 + Delta)),
                ii(j, i)));
    }
    sort(potentialR.begin(), potentialR.end(), cmpPdii);

    double lastR = INF;
    while (!potentialR.empty()) {
        pdii tmp = potentialR.back();
        double tmpR = tmp.first, tmpM = (double)(*sol).workstations.size();
        if (sumRj / tmpM + eps < lastR) {
            double bestR = (sumRj / tmpM + eps >= tmpR) ? sumRj / tmpM : tmpR;
            if (curWorkers <= NConst &&
                (tmpM*bestR*bestR - 2.0*bestR*sumRj + sumSquaredRj + eps < (*sol).SI
                 || (fabs(tmpM*bestR*bestR - 2.0*bestR*sumRj + sumSquaredRj - (*sol).SI) < eps
                     && bestR + eps < (*sol).R))) {
                (*sol).SI      = tmpM*bestR*bestR - 2.0*bestR*sumRj + sumSquaredRj;
                (*sol).R       = bestR;
                (*sol).workers = curWorkers;
            }
        }
        lastR = tmpR;
        while (!potentialR.empty() && fabs(potentialR.back().first - lastR) < eps) {
            tmp = potentialR.back();
            if (tmp.second.first == 3) return;
            if (++curWorkers > NConst) return;
            sumRj        -= wstStats[tmp.second.second].Rj;
            sumSquaredRj -= wstStats[tmp.second.second].Rj * wstStats[tmp.second.second].Rj;
            wstStats[tmp.second.second].workers++;
            wstStats[tmp.second.second].Rj =
                wstStats[tmp.second.second].totalWorktime / (double)wstStats[tmp.second.second].workers;
            sumRj        += wstStats[tmp.second.second].Rj;
            sumSquaredRj += wstStats[tmp.second.second].Rj * wstStats[tmp.second.second].Rj;
            potentialR.pop_back();
        }
    }
}

void calSolutionStat_relaxation(solution* sol) {
    vector<workstationStat> wstStats;
    vector<pdii> potentialR;
    (*sol).SI      = INF;
    (*sol).workers = INF;
    (*sol).R       = INF;
    double sumRj = 0, sumSquaredRj = 0;
    int curWorkers = (int)(*sol).workstations.size();

    for (int i = 0; i < (int)(*sol).workstations.size(); i++) {
        wstStats.push_back(calWorkstationStat((*sol).workstations[i], INF));
        sumRj        += wstStats.back().Rj;
        sumSquaredRj += wstStats.back().Rj * wstStats.back().Rj;
        for (int j = 1; j <= 3; j++)
            potentialR.push_back(pdii(
                wstStats.back().totalWorktime / ((double)j * (1.0 + Delta)),
                ii(j, i)));
    }
    sort(potentialR.begin(), potentialR.end(), cmpPdii);

    double lastR = INF;
    while (!potentialR.empty()) {
        pdii tmp = potentialR.back();
        double tmpR = tmp.first, tmpM = (double)(*sol).workstations.size();
        double bestR = (sumRj / tmpM + eps >= tmpR) ? min(sumRj / tmpM, lastR) : tmpR;
        if (curWorkers <= NConst &&
            (tmpM*bestR*bestR - 2.0*bestR*sumRj + sumSquaredRj + eps < (*sol).SI
             || (fabs(tmpM*bestR*bestR - 2.0*bestR*sumRj + sumSquaredRj - (*sol).SI) < eps
                 && bestR + eps < (*sol).R))) {
            (*sol).SI      = tmpM*bestR*bestR - 2.0*bestR*sumRj + sumSquaredRj;
            (*sol).R       = bestR;
            (*sol).workers = curWorkers;
        }
        lastR = tmpR;
        while (!potentialR.empty() && fabs(potentialR.back().first - lastR) < eps) {
            tmp = potentialR.back();
            if (tmp.second.first == 3) return;
            if (++curWorkers > NConst) return;
            sumRj        -= wstStats[tmp.second.second].Rj;
            sumSquaredRj -= wstStats[tmp.second.second].Rj * wstStats[tmp.second.second].Rj;
            wstStats[tmp.second.second].workers++;
            wstStats[tmp.second.second].Rj =
                wstStats[tmp.second.second].totalWorktime / (double)wstStats[tmp.second.second].workers;
            sumRj        += wstStats[tmp.second.second].Rj;
            sumSquaredRj += wstStats[tmp.second.second].Rj * wstStats[tmp.second.second].Rj;
            potentialR.pop_back();
        }
    }
}

// ─── Print solution ───────────────────────────────────────────────────────────

void printSolution(solution sol) {
    if (sol.workers > NConst) { cout << "No solution" << endl; return; }
    calSolutionStat(&sol);
    int totalWorkers = 0, totalWorkerSaved = 0;
    cout.precision(3);
    cout << "Optimal SI = " << fixed << sol.SI
         << " (R = " << sol.R << ")" << endl;
    for (auto& w : sol.workstations) sort(w.begin(), w.end());
    sort(sol.workstations.begin(), sol.workstations.end());
    cout << (int)sol.workstations.size() << " workstations" << endl;
    for (int i = 0; i < (int)sol.workstations.size(); i++) {
        cout << "Workstation " << i+1 << ":";
        for (int x : sol.workstations[i]) cout << " " << x;
        workstationStat stat = calWorkstationStat(sol.workstations[i], sol.R);
        totalWorkers     += stat.workers;
        totalWorkerSaved += stat.workerSaved;
        cout << " -- W: " << stat.workers << ", S: " << stat.workerSaved
             << ", T: " << stat.totalWorktime << ", Rj: " << stat.Rj
             << " (idle: " << sol.R - stat.Rj << ")" << endl;
    }
    cout << totalWorkers << " workers, " << totalWorkerSaved << " saved" << endl;
}

// ─── Mark / Unmark (thread-local) ────────────────────────────────────────────

void markWorkstation_local(const vector<int>& wst, LocalTaskArr& lt) {
    int curNode = wst[0];
    lt[curNode].status = 0;
    for (int i = 1; i < (int)wst.size(); i++) {
        int x = wst[i];
        for (int v : lt[x].edge)    lt[curNode].edge.push_back(v);
        lt[x].edge.clear();
        for (int v : lt[x].revEdge) lt[curNode].revEdge.push_back(v);
        lt[x].revEdge.clear();
        lt[x].status = -curNode;
    }
}

void unmarkWorkstation_local(const vector<int>& wst, LocalTaskArr& lt) {
    for (int x : wst) {
        lt[x].status     = 1;
        lt[x].edge       = edge_rs[x].edge;
        lt[x].originEdge = edge_rs[x].originEdge;
        lt[x].revEdge    = edge_rs[x].revEdge;
    }
}

// ─── Sequential exhaustive (thread-local state) ───────────────────────────────

void exhaustive_local(int i, int j,
                      vector<int> curWst,
                      solution curRes,
                      LocalTaskArr& lt,
                      solution& localBest)
{
    if (ITERATION_LIMIT >= 0 && iterationCnt.load(memory_order_relaxed) > ITERATION_LIMIT)
        return;

    if (i > N) {
        // Solution hoàn chỉnh
        calSolutionStat(&curRes);
        if (cmpSolution(curRes, localBest)) {
            localBest = curRes;
            // Đẩy ngay vào finalRes và đồng bộ bestSI
            updateFinalRes(localBest);
        }
        int prevCnt = iterationCnt.fetch_add(1, memory_order_relaxed);
        if ((prevCnt + 1) % PRINT_INTERVAL == 0) {
            solution snapshot;
            {
                lock_guard<mutex> lk(finalRes_mutex);
                snapshot = finalRes;
            }
            {
                lock_guard<mutex> lk(print_mutex);
                cout << "[Iteration " << (prevCnt + 1) << "] ";
                if (snapshot.workers > NConst) {
                    cout << "No solution yet" << endl;
                } else {
                    calSolutionStat(&snapshot);
                    cout << "Best so far: SI = " << fixed << setprecision(3)
                         << snapshot.SI << " (R = " << snapshot.R << ")" << endl;
                }
            }
        }
        return;
    }
    else if (curWst.empty()) {
        if (lt[i].status != 1) exhaustive_local(i+1, i+1, curWst, curRes, lt, localBest);
        else {
            curWst.push_back(i);
            exhaustive_local(i, i, curWst, curRes, lt, localBest);
            curWst.pop_back();
        }
    }
    else {
        if ((int)curWst.size() < MAXWSTSIZE) {
            for (int k = j+1; k <= N; k++) {
                if (lt[k].status == 1) {
                    curWst.push_back(k);
                    if (validWorkstation_local(curWst, lt))
                        exhaustive_local(i, k, curWst, curRes, lt, localBest);
                    curWst.pop_back();
                }
            }
        }
        if (validWorkstation_local(curWst, lt)) {
            markWorkstation_local(curWst, lt);
            curRes.workstations.push_back(curWst);

            // Pruning: SI = M*R²-2R*ΣRj+ΣRj² không giảm khi thêm workstation
            // → partial SI đã >= bestSI thì full solution cũng không thể tốt hơn
            calSolutionStat_relaxation(&curRes);
            if (curRes.SI <= getBestSI() + eps) {
                calSolutionStat(&curRes);
                vector<int> newWst;
                exhaustive_local(i+1, i+1, newWst, curRes, lt, localBest);
            }

            unmarkWorkstation_local(curWst, lt);
            curRes.workstations.pop_back();
        }
    }
}

// ─── Parallel search ──────────────────────────────────────────────────────────

void findSolution() {
    iterationCnt.store(0);
    finalRes.workstations.clear();
    finalRes.workers = INF;
    finalRes.SI      = INF;
    finalRes.R       = INF;
    {
        lock_guard<mutex> lk(bestSI_mutex);
    }

    for (int i = 1; i <= N; i++) {
        taskList[i].status     = 1;
        taskList[i].edge       = edge_rs[i].edge;
        taskList[i].originEdge = edge_rs[i].originEdge;
        taskList[i].revEdge    = edge_rs[i].revEdge;
    }

    // Liệt kê các nhánh gốc: workstation đầu tiên {1}, {1,k}, {1,k,m}
    struct Branch {
        vector<int> wst;
        int nextI, nextJ;
    };

    vector<Branch> branches;
    branches.push_back({{1}, 2, 2});

    for (int k = 2; k <= N; k++) {
        vector<int> wst2 = {1, k};
        LocalTaskArr lt0 = makeLocalTasks();
        if (!validWorkstation_local(wst2, lt0)) continue;

        branches.push_back({wst2, 2, 2});

        if (MAXWSTSIZE >= 3) {
            for (int m = k+1; m <= N; m++) {
                vector<int> wst3 = {1, k, m};
                LocalTaskArr lt1 = makeLocalTasks();
                if (validWorkstation_local(wst3, lt1))
                    branches.push_back({wst3, 2, 2});
            }
        }
    }

    // Thread pool
    unsigned int nThreads = max(1u, thread::hardware_concurrency());
    mutex branchMutex;
    int branchIdx = 0;

    auto worker = [&]() {
        while (true) {
            int idx;
            {
                lock_guard<mutex> lk(branchMutex);
                if (branchIdx >= (int)branches.size()) return;
                idx = branchIdx++;
            }

            const Branch& br = branches[idx];

            LocalTaskArr lt = makeLocalTasks();
            solution localBest;
            localBest.workers = INF;
            localBest.SI      = INF;
            localBest.R       = INF;

            markWorkstation_local(br.wst, lt);
            solution curRes;
            curRes.workstations.push_back(br.wst);

            // Pruning ngay tại tầng gốc
            calSolutionStat_relaxation(&curRes);
            if (curRes.SI <= getBestSI() + eps) {
                calSolutionStat(&curRes);
                vector<int> newWst;
                exhaustive_local(br.nextI, br.nextJ, newWst, curRes, lt, localBest);
            }

            updateFinalRes(localBest);
        }
    };

    vector<thread> threads;
    threads.reserve(nThreads);
    for (unsigned int t = 0; t < nThreads; t++)
        threads.emplace_back(worker);
    for (auto& th : threads) th.join();
}

int main() {
    auto wall0 = chrono::steady_clock::now();

    readInput();
    findSolution();
    printSolution(finalRes);

    auto wall1 = chrono::steady_clock::now();
    cout << fixed << setprecision(3)
         << "Wall time : " << chrono::duration<double>(wall1 - wall0).count() << "s" << endl;
    cout << "Total iterations: " << iterationCnt.load() << endl;
    return 0;
}
