#include <bits/stdc++.h>
#include <thread>

using namespace std;

const double eps = 1e-9;
const int INF = 1e9;

const int MAXN = 100; // Maximum number of tasks
const int MAXWSTSIZE = 3;

const int STARTTEMP = 100;
const int DECTEMP = 5;
const double COOLRATE = 1.0/1.027;
const int LOOPTIME = 200;

const int SA_REPEAT = 1; // Ideally SA_REPEAT = 1

// Structure for collecting all possible moves/swaps before parallel processing
struct CandidateMove {
    int srcWst;
    int srcTaskIdx;
    int dstWst;      // == (int)curRes.workstations.size() means "new workstation"
    int dstTaskIdx;  // -1 = move, >= 0 = swap
};

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
    //freopen("Test/TestPL15-1-0.txt", "r", stdin);

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

///* Find a good initial solution

struct solution{
    int workers;
    vector<vector<int>> workstations;
    double R;
    double SI;
};

solution curRes, finalRes;

set<int> reachableTask;
set<int> workstationElements;

bool cmpSolution(solution X, solution Y){
    if(X.workers > NConst) return false;
    if(Y.workers > NConst) return true;
    if(fabs(X.SI - Y.SI) > eps) return X.SI < Y.SI;
    if(fabs(X.R * X.R * (double)X.workstations.size() - Y.R * Y.R * (double)Y.workstations.size()) > eps) return X.R * X.R * (double)X.workstations.size() < Y.R * Y.R * (double)Y.workstations.size();
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

workstationStat calWorkstationStat(vector<int> wst, double R){
    workstationStat stat;
    stat.totalWorktime = 0;
    int baseWorkers = 0;
    for(int i = 0; i < (int)wst.size(); i++){
        stat.totalWorktime += taskList[wst[i]].worktime;
        double time = taskList[wst[i]].worktime;
        if(time <= R) baseWorkers++;
        else if(time <= 2*R) baseWorkers += 2;
        else baseWorkers += 3;
    }

    if(stat.totalWorktime <= R * (1.0 + Delta) + eps){
        stat.workers = 1;
        stat.workerSaved = baseWorkers - 1;
    }
    else if(stat.totalWorktime <= 2 * R * (1.0 + Delta) + eps){
        stat.workers = 2;
        stat.workerSaved = baseWorkers - 2;
    }
    else{
        stat.workers = 3;
        stat.workerSaved = baseWorkers - 3;
    }
    stat.Rj = stat.totalWorktime / stat.workers;
    stat.tasks = (int)wst.size();
    return stat;
}

vector<int> curBestWorkstation;

void cmpWorkstation(vector<int> wst){
    if(rand() % 100 >= 50) curBestWorkstation = wst;
}

void findWorkstation(int t, vector<int> wst, int lastTask){
    if(lastTask != 0){
        taskList[lastTask].status = 2;
        wst.push_back(lastTask);
    }

    if(t == MAXWSTSIZE){
        if(validWorkstation(wst)) cmpWorkstation(wst);
    }
    else{
        findWorkstation(t + 1, wst, 0);
        for(int i = 1; i <= N; i++){
            if(taskList[i].status == 1){
                findWorkstation(t + 1, wst, i);
            }
        }
    }

    if(lastTask != 0){
        taskList[lastTask].status = 1;
        wst.pop_back();
    }
}

typedef pair<int, int> ii;
typedef pair<double, ii> pdii;

bool cmpPdii(pdii X, pdii Y){
    if(fabs(X.first - Y.first) > eps) return X.first < Y.first;
    return false;
}

void calSolutionStat(solution* sol){
    vector<workstationStat> wstStats;
    vector<pdii> potentialR;
    (*sol).SI = INF;
    (*sol).workers = INF;
    (*sol).R = INF;
    double sumRj = 0, sumSquaredRj = 0;
    int curWorkers = (int)(*sol).workstations.size();
    for(int i = 0; i < (int)(*sol).workstations.size(); i++){
        wstStats.push_back(calWorkstationStat((*sol).workstations[i], INF));
        sumRj += wstStats.back().Rj;
        sumSquaredRj += wstStats.back().Rj * wstStats.back().Rj;
        for(int j = 1; j <= 3; j++){
            potentialR.push_back(pdii(wstStats.back().totalWorktime / ((double)j * (double)(1.0 + Delta)), ii(j, i)));
        }
    }
    sort(potentialR.begin(), potentialR.end(), cmpPdii);
    double lastR = INF;
    while(!potentialR.empty()){
        pdii tmp = potentialR.back();
        double tmpR = tmp.first, tmpM = (double)(*sol).workstations.size();
        if(sumRj / tmpM + eps < lastR){
            double bestR;
            if(sumRj / tmpM + eps >= tmpR) bestR = sumRj / tmpM;
            else bestR = tmpR;
            if(curWorkers <= NConst &&
               (tmpM * bestR * bestR - 2.0 * bestR * sumRj + sumSquaredRj + eps < (*sol).SI
                || (fabs(tmpM * bestR * bestR - 2.0 * bestR * sumRj + sumSquaredRj - (*sol).SI) < eps && bestR + eps < (*sol).R))){
                (*sol).SI = tmpM * bestR * bestR - 2.0 * bestR * sumRj + sumSquaredRj;
                (*sol).R = bestR;
                (*sol).workers = curWorkers;
            }
        }
        lastR = tmpR;
        while(!potentialR.empty() && fabs(potentialR.back().first - lastR) < eps){
            tmp = potentialR.back();
            if(tmp.second.first == 3) return;
            if(++curWorkers > NConst) return;
            sumRj -= wstStats[tmp.second.second].Rj;
            sumSquaredRj -= wstStats[tmp.second.second].Rj * wstStats[tmp.second.second].Rj;
            wstStats[tmp.second.second].workers++;
            wstStats[tmp.second.second].Rj = wstStats[tmp.second.second].totalWorktime / (double)wstStats[tmp.second.second].workers;
            sumRj += wstStats[tmp.second.second].Rj;
            sumSquaredRj += wstStats[tmp.second.second].Rj * wstStats[tmp.second.second].Rj;
            potentialR.pop_back();
        }
    }
}

///* Print solution

void printSolution(solution sol){
    if(sol.workers > NConst){
        cout << "No solution" << endl;
        return;
    }

    calSolutionStat(&sol);
    int totalWorkers = 0;
    int totalWorkerSaved = 0;
    int balancedGroups = 0;

    cout.precision(3);
    cout << "Optimal SI = " << fixed << sol.SI << " (R = " << sol.R << ")" << endl;

    for(int i = 0; i < (int)sol.workstations.size(); i++)
        sort(sol.workstations[i].begin(), sol.workstations[i].end());
    sort(sol.workstations.begin(), sol.workstations.end());

    cout << (int)sol.workstations.size() << " workstations" << endl;
    for(int i = 0; i < (int)sol.workstations.size(); i++){
        cout << "Workstation " << i + 1 << ":";
        for(int j = 0; j < (int)sol.workstations[i].size(); j++){
            cout << " " << sol.workstations[i][j];
        }

        workstationStat stat = calWorkstationStat(sol.workstations[i], sol.R);
        totalWorkers += stat.workers;
        totalWorkerSaved += stat.workerSaved;
        cout << " -- W: " << stat.workers << ", S: " << stat.workerSaved << ", T: " << stat.totalWorktime <<", Rj: " << stat.Rj << " (idle: " << sol.R - stat.Rj << ")" << endl;
    }

    cout << totalWorkers << " workers, " << totalWorkerSaved << " saved" << endl;
}

void resetAllVariable()
{
    finalRes.workstations.clear();
    finalRes.workers = INF;
    finalRes.SI = INF;
    finalRes.R = INF;

    curRes.workstations.clear();
    curRes.workers = INF;
    curRes.SI = INF;
    curRes.R = INF;

    for(int i = 1; i <= N; i++){
        taskList[i].status = 1;
        taskList[i].edge.clear();
        taskList[i].originEdge.clear();
        taskList[i].revEdge.clear();
        for (int a1 = 0; a1 < edge_rs[i].edge.size(); a1++)
        {
            taskList[i].edge.push_back(edge_rs[i].edge[a1]);
        }
        for (int a1 = 0; a1 < edge_rs[i].originEdge.size(); a1++)
        {
            taskList[i].originEdge.push_back(edge_rs[i].originEdge[a1]);
        }
        for (int a1 = 0; a1 < edge_rs[i].revEdge.size(); a1++)
        {
            taskList[i].revEdge.push_back(edge_rs[i].revEdge[a1]);
        }
    }

}

void findSolution(){
    resetAllVariable();

    while(true){
    	bool remain = false;
    	int zeroInDegreeNode = -1;
    	for(int u = 1; u <= N; u++){
    		if(taskList[u].status != 1) continue;
    		bool zeroInDegree = true;
    		for(int i = 0; i < (int)taskList[u].revEdge.size(); i++){
    			int x = taskList[u].revEdge[i];
    			if(taskList[x].status <= 0) continue;
    			zeroInDegree = false;
    		}
    		if(zeroInDegree){
    			zeroInDegreeNode = u;
    			remain = true;
    			break;
    		}
    	}
    	if(!remain) break;

        int curNode = zeroInDegreeNode;
        curBestWorkstation.clear();
        curBestWorkstation.push_back(curNode);
        vector<int> workstation;
        findWorkstation(1, workstation, curNode);

        taskList[curNode].status = 0;
        for(int j = 1; j < (int)curBestWorkstation.size(); j++){
            int x = curBestWorkstation[j];
            for(int k = 0; k < (int)taskList[x].edge.size(); k++)
                taskList[curNode].edge.push_back(taskList[x].edge[k]);
            taskList[x].edge.clear();

            for(int k = 0; k < (int)taskList[x].revEdge.size(); k++)
                taskList[curNode].revEdge.push_back(taskList[x].revEdge[k]);
            taskList[x].revEdge.clear();

            taskList[x].status = -curNode;
        }

        curRes.workstations.push_back(curBestWorkstation);
    }

    calSolutionStat(&curRes);
    finalRes = curRes;
    //cout << "R = " << R << ", N' = " << finalRes.workers << endl;
}

///* Tune solution

thread_local int visits[MAXN + 5];
thread_local int visitsCnt = 0;

int findWorkstationIndex(int u, solution* sol){
    for(int i = 0; i < (int)(*sol).workstations.size(); i++){
        for(int j = 0; j < (int)(*sol).workstations[i].size(); j++){
            if((*sol).workstations[i][j] == u) return i;
        }
    }
}

bool dfs2(int u, int curWorkstationIndex, solution* sol){
    visits[u] = visitsCnt;
    int uWorkstationIndex = findWorkstationIndex(u, sol);

    for(int i = 0; i < (int)(*sol).workstations[uWorkstationIndex].size(); i++){
        int v = (*sol).workstations[uWorkstationIndex][i];
        if(visits[v] != visitsCnt && dfs2(v, curWorkstationIndex, sol)) return true;
    }

    for(int i = 0; i < (int)taskList[u].originEdge.size(); i++){
        int v = taskList[u].originEdge[i], vWorkstationIndex = findWorkstationIndex(v, sol);
        if(uWorkstationIndex != curWorkstationIndex && vWorkstationIndex == curWorkstationIndex) return true;
        if(visits[v] == visitsCnt) continue;
        if(dfs2(v, curWorkstationIndex, sol)) return true;
    }

    return false;
}

bool validSolution(solution* sol){
    for(int i = 0; i < (int)(*sol).workstations.size(); i++)
        if(tooLargeOrBadPair((*sol).workstations[i])) return false;

    // no cycle between 2 workstations
    for(int i = 0; i < (int)(*sol).workstations.size(); i++){
        visitsCnt++;
        if(dfs2((*sol).workstations[i][0], i, sol)) return false;
    }

    return true;
}

solution getNeighbor(int choice){
    int W = (int)curRes.workstations.size();
    vector<CandidateMove> candidates;

    // Collect MOVE candidates (move task i,j -> workstation k, or to new workstation)
    for(int i = 0; i < W; i++){
        for(int j = 0; j < (int)curRes.workstations[i].size(); j++){
            for(int k = 0; k <= W; k++){  // k == W means new workstation
                if(k == i) continue;
                if(k < i && (int)curRes.workstations[i].size() == 1 && (int)curRes.workstations[k].size() == 1) continue;
                if(k == W && (int)curRes.workstations[i].size() <= 1) continue;
                candidates.push_back({i, j, k, -1});
            }
        }
    }

    // Collect SWAP candidates
    for(int i = 0; i < W; i++){
        for(int j = 0; j < (int)curRes.workstations[i].size(); j++){
            for(int k = i+1; k < W; k++){
                for(int t = 0; t < (int)curRes.workstations[k].size(); t++){
                    if((int)curRes.workstations[i].size() == 1 && (int)curRes.workstations[k].size() == 1) continue;
                    candidates.push_back({i, j, k, t});
                }
            }
        }
    }

    if(candidates.empty()) return curRes;

    // ==================== LOCK-FREE PARALLEL ====================
    unsigned int numThreads = std::thread::hardware_concurrency();
    if(numThreads == 0) numThreads = 12u;

    vector<vector<solution>> threadSolLists(numThreads);

    auto applyCandidate = [&](const CandidateMove& cand, unsigned int threadId){
        solution tempRes = curRes;
        int i = cand.srcWst, j = cand.srcTaskIdx, k = cand.dstWst;

        if(cand.dstTaskIdx == -1){ // MOVE
            if(k < (int)tempRes.workstations.size()){
                tempRes.workstations[k].push_back(tempRes.workstations[i][j]);
                tempRes.workstations[i].erase(tempRes.workstations[i].begin() + j);
                if(tempRes.workstations[i].empty()) tempRes.workstations.erase(tempRes.workstations.begin() + i);
            } else {
                // move to new workstation
                vector<int> newWst; newWst.push_back(tempRes.workstations[i][j]);
                tempRes.workstations.push_back(newWst);
                tempRes.workstations[i].erase(tempRes.workstations[i].begin() + j);
            }
        } else { // SWAP
            int t = cand.dstTaskIdx;
            tempRes.workstations[i].push_back(tempRes.workstations[k][t]);
            tempRes.workstations[k].push_back(tempRes.workstations[i][j]);
            tempRes.workstations[i].erase(tempRes.workstations[i].begin() + j);
            tempRes.workstations[k].erase(tempRes.workstations[k].begin() + t);
        }

        if(validSolution(&tempRes)){
            calSolutionStat(&tempRes);
            threadSolLists[threadId].push_back(std::move(tempRes));
        }
    };

    std::vector<std::thread> threads;
    size_t total = candidates.size();
    size_t chunkSize = (total + numThreads - 1) / numThreads;

    for(unsigned int th = 0; th < numThreads; ++th){
        size_t start = th * chunkSize;
        size_t end = std::min(start + chunkSize, total);
        if(start >= end) break;
        threads.emplace_back([&, start, end, th](){
            for(size_t idx = start; idx < end; ++idx){
                applyCandidate(candidates[idx], th);
            }
        });
    }
    for(auto& thrd : threads) thrd.join();

    // Merge results from all threads (single-threaded, no race condition)
    vector<solution> solList;
    for(auto& vec : threadSolLists){
        for(auto& s : vec){
            if(cmpSolution(s, finalRes)) finalRes = s;
            solList.push_back(std::move(s));
        }
    }

    if(solList.empty()) return curRes;

    // SA-basic: random pick uniformly from ALL feasible neighbors
    // (no sort, no top-k selection)
    return solList[rand() % (int)solList.size()];
}

void tuneSolution(){
    ///* Simulated annealing
    int temperature = STARTTEMP;
    int choice = (STARTTEMP - 1) / DECTEMP + 1;

    while(temperature > 0){
        for(int i = 1; i <= LOOPTIME; i++){
            solution tempRes = getNeighbor(choice);
            if(tempRes.workstations == curRes.workstations) break;
            if(cmpSolution(tempRes, curRes)) curRes = tempRes;
            else if(rand() % STARTTEMP + 1 <= temperature) curRes = tempRes;
        }

        temperature -= DECTEMP;
        choice--;
        //cout << "T = " << temperature << endl;
        //printSolution(finalRes);
    }
}

///* Find solution

solution SAforALBP1(){
    solution bestRes;
    for(int t = 1; t <= SA_REPEAT; t++){
        findSolution();
        tuneSolution();
        if(t == 1) bestRes = finalRes;
        else if(cmpSolution(finalRes, bestRes)) bestRes = finalRes;
    }
    return bestRes;
}

int main(){
    auto wall0 = chrono::steady_clock::now();

    srand(time(NULL));
    readInput();
    printSolution(SAforALBP1());

    auto wall1 = chrono::steady_clock::now();

    double wallSec = chrono::duration<double>(wall1 - wall0).count();

    cout << fixed << setprecision(3);
    cout << "Wall time : " << wallSec << "s" << endl;
    return 0;
}
