#include <bits/stdc++.h>

using namespace std;

const double eps = 1e-9;
const int INF = 1e9;

const int MAXN = 100; // Maximum number of tasks
const int MAXWSTSIZE = 3;

const int ITERATION_LIMIT = -1; // = -1 for a full search
int iterationCnt;

const double TIME_LIMIT_SEC = 43200.0; // Time limit in seconds, set to -1 for no limit
chrono::steady_clock::time_point startTime;

///* Read input

struct task{
    string machine;
    string machine_name;
    int type;
    double worktime;
    int status;
    int level;
    vector<int> edge, originEdge;
    vector<int> revEdge;
};

struct edge_reserve{
    vector<int> edge, originEdge;
    vector<int> revEdge;
};

struct workstation{
    int worker;
    int index;
    bool isStart = false;
    bool isEnd = false;
    vector<int> edge;
};

int N, NConst;
double Delta;
task taskList[MAXN + 5];
edge_reserve edge_rs[MAXN + 5];

void readInput(){
    //freopen("Test/TestPL15-1.txt", "r", stdin);

    cin >> N >> NConst >> Delta;
    Delta /= 100.0;
    for(int i = 1; i <= N; i++){
        int ign;
        cin >> ign >> taskList[i].machine >> taskList[i].type >> taskList[i].worktime >> taskList[i].level ;
        taskList[i].status = 1;
    }

    int M; cin >> M;
    while(M--){
        int u, v; cin >> u >> v;
        taskList[u].edge.push_back(v); taskList[u].originEdge.push_back(v);
        taskList[v].revEdge.push_back(u);
        edge_rs[u].edge.push_back(v); edge_rs[u].originEdge.push_back(v);
        edge_rs[v].revEdge.push_back(u);
    }
}

///* Find a good solution

struct solution {
    int workers;
    vector<vector<int>> workstations;
    double R;
    double avgRj;
    double idleTime;
    bool minusEpsilon;
};

solution finalRes;

set<int> reachableTask;
set<int> workstationElements;

bool cmpSolution(solution X, solution Y){
    if (X.workers > NConst) return false;
    if (Y.workers > NConst) return true;
    if (fabs(X.idleTime - Y.idleTime) > eps) return X.idleTime < Y.idleTime;
    if (fabs(X.R * (double)X.workstations.size() - Y.R * (double)Y.workstations.size()) > eps) return X.R * (double)X.workstations.size() < Y.R * (double)Y.workstations.size();
    if (X.minusEpsilon == false && Y.minusEpsilon == true) return true;
    return false;
}

bool dfs1(int u, int rev){
    if(rev == -1
       && workstationElements.find(u) == workstationElements.end()
       && reachableTask.find(u) != reachableTask.end())
        return true;

    reachableTask.insert(u * rev);

    if(rev == 1){
        for(int i = 0; i < (int)taskList[u].edge.size(); i++){
            int v = taskList[u].edge[i];
            if(taskList[v].status < 0) v = -taskList[v].status;
            if(reachableTask.find(v * rev) == reachableTask.end())
                dfs1(v, rev);
        }
    }
    else{
        for(int i = 0; i < (int)taskList[u].revEdge.size(); i++){
            int v = taskList[u].revEdge[i];
            if(taskList[v].status < 0) v = -taskList[v].status;
            if(reachableTask.find(v * rev) == reachableTask.end() && dfs1(v, rev))
                return true;
        }
    }

    return false;
}

bool tooLargeOrBadPair(vector<int> wst){
    // not more than MAXWSTSIZE tasks
    if((int)wst.size() > MAXWSTSIZE) return true;

    // not more than 2 machine
    set<string> machine;
    for(int i = 0; i < (int)wst.size(); i++)
        machine.insert(taskList[wst[i]].machine);
    if((int)machine.size() > 2) return true;

    // no 1-1 or 1-2 pair
    set<int> type;
    for(int i = 0; i < (int)wst.size(); i++)
        type.insert(taskList[wst[i]].type);
    if((int)machine.size() == 2){
        if((int)type.size() == 1 && type.find(1) != type.end()) return true;
        if(type.find(1) != type.end() && type.find(2) != type.end()) return true;
    }

    //
    return false;
}

bool validWorkstation(vector<int> wst){
    if(tooLargeOrBadPair((wst))) return false;

    // no cycle between 2 workstations
    reachableTask.clear();
    workstationElements.clear();
    for(int i = 0; i < (int)wst.size(); i++){
        workstationElements.insert(wst[i]);
        dfs1(wst[i], 1);
    }
    for(int i = 0; i < (int)wst.size(); i++)
        if(dfs1(wst[i], -1)) return false;

    return true;
}

struct workstationStat{
    int workers;
    int workerSaved;
    int tasks;
    double totalWorktime;
    double Rj;
};

workstationStat calWorkstationStat(vector<int> wst, double R, bool minusEpsilon){
    workstationStat stat; stat.totalWorktime = 0;
    int baseWorkers = 0;
    for (int x : wst) {
        stat.totalWorktime += taskList[x].worktime;
        double t = taskList[x].worktime;
        if(t <= R*(1.0 + Delta) + eps){
            if(fabs(t - R*(1.0 + Delta)) < eps && minusEpsilon) baseWorkers += 2;
            else baseWorkers++;
        }
        else if(t <= 2.0*R*(1.0 + Delta) + eps){
            if(fabs(t - 2.0*R*(1.0 + Delta)) < eps && minusEpsilon) baseWorkers += 3;
            else baseWorkers += 2;
        }
        else baseWorkers += 3;
    }
    if(stat.totalWorktime <= R*(1.0 + Delta) + eps){
        if(fabs(stat.totalWorktime - R*(1.0 + Delta)) < eps && minusEpsilon) stat.workers = 2;
        else stat.workers = 1;
    }
    else if(stat.totalWorktime <= 2.0*R*(1.0 + Delta) + eps){
        if(fabs(stat.totalWorktime - 2.0*R*(1.0 + Delta)) < eps && minusEpsilon) stat.workers = 3;
        else stat.workers = 2;
    }
    else stat.workers = 3;
    stat.workerSaved = baseWorkers - stat.workers;
    stat.Rj   = stat.totalWorktime / stat.workers;
    stat.tasks = (int)wst.size();
    return stat;
}

typedef pair<int, int> ii;
typedef pair<double, ii> pdii;

bool cmpPdii(pdii X, pdii Y){
    if (fabs(X.first - Y.first) > eps) return X.first < Y.first;
    return X.second.first < Y.second.first;
}

void calSolutionStat(solution* sol) {
    vector<workstationStat> wstStats;
    vector<pdii> potentialR;
    (*sol).idleTime = INF;
    (*sol).workers  = INF;
    (*sol).R        = INF;
    (*sol).avgRj    = INF;
    (*sol).minusEpsilon = false;

    double sumRj = 0, sumSignedRj = 0, cycleCoef = (double)(*sol).workstations.size();
    int curWorkers = (int)(*sol).workstations.size();
    for (int i = 0; i < (int)(*sol).workstations.size(); i++) {
        wstStats.push_back(calWorkstationStat((*sol).workstations[i], INF, false));
        sumRj += wstStats.back().Rj;
        sumSignedRj -= wstStats.back().Rj;
        for (int j = 1; j <= 3; j++){
            potentialR.push_back(pdii(wstStats.back().totalWorktime / (double)j, ii(j,i)));
            potentialR.push_back(pdii(wstStats.back().totalWorktime / (double)j / (1.0 + Delta), ii(-j,i)));
        }
    }
    sort(potentialR.begin(), potentialR.end(), cmpPdii);

    double lastR = INF;
    while (!potentialR.empty()) {
        pdii tmp = potentialR.back();
        if (curWorkers <= NConst){
            if(cycleCoef > -eps){
                if(sumRj / (double)(*sol).workstations.size() + eps < lastR){
                    double candidateR = max(tmp.first, sumRj / (double)(*sol).workstations.size());
                    if(cycleCoef * candidateR + sumSignedRj + eps < (*sol).idleTime
                       || (fabs(cycleCoef * candidateR + sumSignedRj - (*sol).idleTime) < eps
                           && candidateR + eps < (*sol).R)
                       || (fabs(cycleCoef * candidateR + sumSignedRj - (*sol).idleTime) < eps
                           && fabs(candidateR - (*sol).R) < eps
                           && (*sol).minusEpsilon == true)){
                        (*sol).idleTime = cycleCoef * candidateR + sumSignedRj;
                        (*sol).workers  = curWorkers;
                        (*sol).R        = candidateR;
                        (*sol).avgRj    = sumRj / (double)(*sol).workstations.size();
                        (*sol).minusEpsilon = false;
                    }
                }
            }
            else{
                if(sumRj / (double)(*sol).workstations.size() + eps < lastR){
                    double candidateR = lastR;
                    if(cycleCoef * candidateR + sumSignedRj + eps < (*sol).idleTime
                       || (fabs(cycleCoef * candidateR + sumSignedRj - (*sol).idleTime) < eps
                           && candidateR + eps < (*sol).R)){
                        (*sol).idleTime = cycleCoef * candidateR + sumSignedRj;
                        (*sol).workers  = curWorkers;
                        (*sol).R        = candidateR;
                        (*sol).avgRj    = sumRj / (double)(*sol).workstations.size();
                        (*sol).minusEpsilon = true;
                    }
                }
            }
        }

        lastR = tmp.first;
        while(!potentialR.empty() && fabs(potentialR.back().first - lastR) < eps){
            tmp = potentialR.back();
            if(tmp.second.first == -3) return;
            if(tmp.second.first < 0 && curWorkers + 1 > NConst) return;
            if(tmp.second.first < 0){
                sumRj -= wstStats[tmp.second.second].Rj;
                sumSignedRj -= wstStats[tmp.second.second].Rj;
                cycleCoef++;
                curWorkers++;
                wstStats[tmp.second.second].workers++;
                wstStats[tmp.second.second].Rj =
                    wstStats[tmp.second.second].totalWorktime / (double)wstStats[tmp.second.second].workers;
                sumRj += wstStats[tmp.second.second].Rj;
                sumSignedRj -= wstStats[tmp.second.second].Rj;
                cycleCoef++;
            }
            else{
                sumSignedRj += 2.0 * wstStats[tmp.second.second].Rj;
                cycleCoef -= 2;
            }
            potentialR.pop_back();
        }
    }
}

///* Print solution

void printSolution(solution sol) {
    if (sol.workers > NConst) { cout << "No solution" << endl; return; }
    calSolutionStat(&sol);
    int totalWorkers = 0, totalWorkerSaved = 0;
    double totalRj = 0;
    cout.precision(3);
    cout << "Optimal idleTime = " << fixed << sol.idleTime
         << " (R = " << sol.R; if(sol.minusEpsilon) cout << "-e"; cout << ", ";
    cout << "avgRj = " << sol.avgRj << ")" << endl;
    for (auto& w : sol.workstations) sort(w.begin(), w.end());
    sort(sol.workstations.begin(), sol.workstations.end());
    cout << (int)sol.workstations.size() << " workstations" << endl;
    for (int i = 0; i < (int)sol.workstations.size(); i++) {
        cout << "Workstation " << i+1 << ":";
        for (int x : sol.workstations[i]) cout << " " << x;
        workstationStat stat = calWorkstationStat(sol.workstations[i], sol.R, sol.minusEpsilon);
        totalRj          += stat.Rj;
        totalWorkers     += stat.workers;
        totalWorkerSaved += stat.workerSaved;
        cout << " -- W: " << stat.workers << ", S: " << stat.workerSaved
             << ", T: " << stat.totalWorktime << ", Rj: " << stat.Rj
             << " (idle: " << sol.R - stat.Rj << ")" << endl;
    }
    cout << totalWorkers << " workers, " << totalWorkerSaved << " saved" << endl;
}

void printSolutionLight(solution sol){
    for(int i = 0; i < (int)sol.workstations.size(); i++)
        sort(sol.workstations[i].begin(), sol.workstations[i].end());
    sort(sol.workstations.begin(), sol.workstations.end());
    for(int i = 0; i < (int)sol.workstations.size(); i++){
        cout << "(";
        for(int j = 0; j < (int)sol.workstations[i].size(); j++){
            if(j > 0) cout << ",";
            cout << sol.workstations[i][j];
        }
        cout << ") ";
    }
    cout << endl;
}

void markWorkstation(vector<int> wst){
    int curNode = wst[0];
    taskList[curNode].status = 0;
    for(int i = 1; i < (int)wst.size(); i++){
        int x = wst[i];
        for(int k = 0; k < (int)taskList[x].edge.size(); k++)
            taskList[curNode].edge.push_back(taskList[x].edge[k]);
        taskList[x].edge.clear();

        for(int k = 0; k < (int)taskList[x].revEdge.size(); k++)
            taskList[curNode].revEdge.push_back(taskList[x].revEdge[k]);
        taskList[x].revEdge.clear();

        taskList[x].status = -curNode;
    }
}

void unmarkWorkstation(vector<int> wst){
    for(int i = 0; i < (int)wst.size(); i++){
        int x = wst[i];
        taskList[x].status = 1;
        taskList[x].edge = edge_rs[x].edge;
        taskList[x].originEdge = edge_rs[x].originEdge;
        taskList[x].revEdge = edge_rs[x].revEdge;
    }
}

vector<int> createShuffledVector(int j) {
    std::vector<int> vec;
    vec.reserve(N - j);
    for (int i = j + 1; i <= N; ++i) {
        vec.push_back(i);
    }

    std::random_device rd;
    std::mt19937 g(rd());
    std::shuffle(vec.begin(), vec.end(), g);

    return vec;
}

void exhaustive(int i, int j, vector<int> curWst, solution curRes){
    if(ITERATION_LIMIT >= 0 && iterationCnt > ITERATION_LIMIT) return; // Early termination by iteration
    if(TIME_LIMIT_SEC >= 0){
        double elapsed = chrono::duration<double>(chrono::steady_clock::now() - startTime).count();
        if(elapsed > TIME_LIMIT_SEC) return; // Early termination by time
    }

    if(i > N){
        calSolutionStat(&curRes);
        if(cmpSolution(curRes, finalRes)) finalRes = curRes;
        iterationCnt++;
        /*
        if(iterationCnt % 100000 == 0){
            cout << "Iteration: " << iterationCnt << endl;
            printSolution(finalRes);
        }
        //*/
        return;
    }
    else if(curWst.empty()){
        if(taskList[i].status != 1) exhaustive(i+1, i+1, curWst, curRes);
        else{
            curWst.push_back(i);
            exhaustive(i, i, curWst, curRes);
            curWst.pop_back();
        }
    }
    else{
        if((int)curWst.size() < MAXWSTSIZE){
            /*
            vector<int> potentialPos = createShuffledVector(j);
            for(int t = 0; t < (int)potentialPos.size(); t++){
                int k = potentialPos[t];
            */
            for(int k = j + 1; k <= N; k++){
                if(taskList[k].status == 1){
                    curWst.push_back(k);
                    if(validWorkstation(curWst)) exhaustive(i, k, curWst, curRes);
                    curWst.pop_back();
                }
            }
        }
        if(validWorkstation(curWst)){
            markWorkstation(curWst);
            curRes.workstations.push_back(curWst);
            vector<int> newWst;
            exhaustive(i+1, i+1, newWst, curRes);
            unmarkWorkstation(curWst);
            curRes.workstations.pop_back();
        }
    }
}

void resetAllVariable()
{
    iterationCnt = 0;
    startTime = chrono::steady_clock::now();

    finalRes.workstations.clear();
    finalRes.workers = INF;
    finalRes.idleTime = INF;
    finalRes.R = INF;

    for(int i = 1; i <= N; i++){
        taskList[i].status = 1;
        taskList[i].edge = edge_rs[i].edge;
        taskList[i].originEdge = edge_rs[i].originEdge;
        taskList[i].revEdge = edge_rs[i].revEdge;
    }

}

void findSolution(){
    resetAllVariable();

    vector<int> curWst;
    solution curRes;
    exhaustive(1, 1, curWst, curRes);
}

int main(){
    auto wall0 = chrono::steady_clock::now();

    readInput();
    findSolution();
    double elapsed = chrono::duration<double>(chrono::steady_clock::now() - wall0).count();
    bool timeLimited = TIME_LIMIT_SEC >= 0 && elapsed >= TIME_LIMIT_SEC;
    if(timeLimited)
        cout << "Search stopped early (time limit: " << TIME_LIMIT_SEC << "s). Result may not be optimal." << endl;
    printSolution(finalRes);

    auto wall1 = chrono::steady_clock::now();

    double wallSec = chrono::duration<double>(wall1 - wall0).count();

    cout << fixed << setprecision(3);
    cout << "Wall time : " << wallSec << "s" << endl;
    return 0;
}
