"""
Solve PALBP-E-IT using OR-Tools CP-SAT.
Usage: python solve_ortools.py < input.txt
Global parameters Q=3, P=3. Scaling by lcm(1..Q) for integer arithmetic.
"""

import sys
import math
import time
from ortools.sat.python import cp_model

Q = 3
P = 3
SCALE = math.lcm(*range(1, Q + 1))  # 6 for Q=3

def parse_input(lines):
    idx = 0
    M = int(lines[idx]); idx += 1
    N_hat = int(lines[idx]); idx += 1
    t = []
    for _ in range(M):
        parts = lines[idx].split(); idx += 1
        t.append(int(parts[3]) if len(parts) >= 4 else int(parts[0]))
    num_edges = int(lines[idx]); idx += 1
    edges = []
    for _ in range(num_edges):
        u, v = map(int, lines[idx].split()); idx += 1
        edges.append((u - 1, v - 1))
    return M, N_hat, t, edges

def solve(M, N_hat, t, edges):
    T_bar  = sum(t)
    W_max  = M
    sT_bar = SCALE * T_bar

    model = cp_model.CpModel()

    # g[i]: group of task i, 0-indexed internally (1..W_max displayed)
    g = [model.NewIntVar(0, W_max - 1, f"g_{i}") for i in range(M)]

    # For each group j: in_ij = (g[i] == j)
    in_ = {}
    for i in range(M):
        for j in range(W_max):
            b = model.NewBoolVar(f"in_{i}_{j}")
            model.Add(g[i] == j).OnlyEnforceIf(b)
            model.Add(g[i] != j).OnlyEnforceIf(b.Not())
            in_[i, j] = b

    # active[j] = OR of in_[i,j]
    active = [model.NewBoolVar(f"active_{j}") for j in range(W_max)]
    for j in range(W_max):
        model.AddBoolOr([in_[i, j] for i in range(M)]).OnlyEnforceIf(active[j])
        model.AddBoolAnd([in_[i, j].Not() for i in range(M)]).OnlyEnforceIf(active[j].Not())

    # (1) Precedence
    for (ut, vt) in edges:
        model.Add(g[ut] <= g[vt])

    # (2) Max P tasks per group
    for j in range(W_max):
        model.Add(sum(in_[i, j] for i in range(M)) <= P)

    # (3) n[j]: workers in group j (0 if inactive, 1..Q if active)
    n = [model.NewIntVar(0, Q, f"n_{j}") for j in range(W_max)]
    for j in range(W_max):
        model.Add(n[j] == 0).OnlyEnforceIf(active[j].Not())
        model.Add(n[j] >= 1).OnlyEnforceIf(active[j])

    # (4) Total workers
    if N_hat < 10**7:
        model.Add(sum(n) <= N_hat)

    # (5) sT[j] = SCALE * sum(t_i * in_[i,j])
    sT = [model.NewIntVar(0, sT_bar, f"sT_{j}") for j in range(W_max)]
    for j in range(W_max):
        contribs = []
        for i in range(M):
            c = model.NewIntVar(0, SCALE * t[i], f"c_{i}_{j}")
            model.Add(c == SCALE * t[i]).OnlyEnforceIf(in_[i, j])
            model.Add(c == 0).OnlyEnforceIf(in_[i, j].Not())
            contribs.append(c)
        model.Add(sT[j] == sum(contribs))

    # (6) sCj[j] * n[j] == sT[j]
    #     When inactive: sT[j]=0, n[j]=0 => sCj=0 (we fix directly)
    sCj = [model.NewIntVar(0, sT_bar, f"sCj_{j}") for j in range(W_max)]
    for j in range(W_max):
        model.Add(sCj[j] == 0).OnlyEnforceIf(active[j].Not())
        # For active groups, enumerate n_j in {1..Q}
        for k in range(1, Q + 1):
            is_k = model.NewBoolVar(f"is_k_{j}_{k}")
            model.Add(n[j] == k).OnlyEnforceIf(is_k)
            model.Add(n[j] != k).OnlyEnforceIf(is_k.Not())
            # sCj[j] * k == sT[j] when n[j]==k
            # sCj[j] = sT[j] * (SCALE/k) / SCALE = sT[j] / k
            # Since SCALE = lcm, SCALE/k is integer
            factor = SCALE // k
            prod = model.NewIntVar(0, sT_bar, f"prod_{j}_{k}")
            # prod = sT[j] * factor / SCALE -- but sT[j] = SCALE * T_j, so
            # sCj = SCALE * T_j / k = sT[j] / k
            # Use: sCj[j] * k == sT[j] when active with k workers
            model.Add(sCj[j] * k == sT[j]).OnlyEnforceIf(is_k)

    # (7) sC = max(sCj) -- minimization drives this to max
    sC = model.NewIntVar(0, sT_bar, "sC")
    for j in range(W_max):
        model.Add(sC >= sCj[j])

    # Symmetry: active groups come first
    for j in range(W_max - 1):
        model.Add(active[j] >= active[j + 1])

    # (8) Objective
    # sIT = sum over active j of (sC - sCj[j])
    # W   = sum(active)
    # Secondary: W * sC
    W_var = model.NewIntVar(0, W_max, "W")
    model.Add(W_var == sum(active))

    # sIT_j = (sC - sCj[j]) * active[j]
    sIT_terms = []
    for j in range(W_max):
        diff = model.NewIntVar(0, sT_bar, f"diff_{j}")
        model.Add(diff == sC - sCj[j]).OnlyEnforceIf(active[j])
        model.Add(diff == 0).OnlyEnforceIf(active[j].Not())
        sIT_terms.append(diff)

    sIT = model.NewIntVar(0, W_max * sT_bar, "sIT")
    model.Add(sIT == sum(sIT_terms))

    LC = model.NewIntVar(0, W_max * sT_bar, "LC")
    model.AddMultiplicationEquality(LC, [W_var, sC])

    BIG = W_max * sT_bar + 1
    model.Minimize(sIT * BIG + LC)

    # Solve
    class ProgressCallback(cp_model.CpSolverSolutionCallback):
        def __init__(self, scale, w_max, active, n, g, sCj, sC, sIT, W_var, M, start_time):
            cp_model.CpSolverSolutionCallback.__init__(self)
            self._scale = scale
            self._w_max = w_max
            self._active = active
            self._n = n
            self._g = g
            self._sCj = sCj
            self._sC = sC
            self._sIT = sIT
            self._W_var = W_var
            self._M = M
            self._start = start_time
            self._best_it = float('inf')
            self._count = 0

        def on_solution_callback(self):
            self._count += 1
            it  = self.Value(self._sIT) / self._scale
            lc  = self.Value(self._W_var) * self.Value(self._sC) / self._scale
            elapsed = time.time() - self._start
            if it < self._best_it:
                self._best_it = it
                bar_len = 40
                # Progress bar based on IT improvement (lower bound = 0)
                fill = int(bar_len * max(0, 1 - it / (self._scale * sum(1 for _ in range(self._w_max)))))
                bar = '#' * fill + '-' * (bar_len - fill)
                print(f"\r  [{bar}] sol#{self._count:>3d} | IT={it:.4f}  LC={lc:.4f}  t={elapsed:.2f}s",
                      end='', flush=True)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 43200.0
    solver.parameters.num_search_workers = 24
    print("Solving...")
    solve_start = time.time()
    cb = ProgressCallback(SCALE, W_max, active, n, g, sCj, sC, sIT, W_var, M, solve_start)
    status = solver.Solve(model, cb)
    print()  # newline after progress bar

    status_name = solver.StatusName(status)
    print(f"\nStatus: {status_name}")

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sC_val  = solver.Value(sC)
        W_val   = solver.Value(W_var)
        sIT_val = solver.Value(sIT)
        C_val   = sC_val / SCALE
        IT_val  = sIT_val / SCALE
        print(f"C        = {C_val:.4f}")
        print(f"W        = {W_val}")
        print(f"LC (W*C) = {W_val * C_val:.4f}")
        print(f"IT       = {IT_val:.4f}")
        print(f"Optimal  = {status == cp_model.OPTIMAL}")
        print("\nGroup assignments:")
        total_workers = 0
        for j in range(W_max):
            if solver.Value(active[j]) == 1:
                tasks = [i+1 for i in range(M) if solver.Value(g[i]) == j]
                n_val = solver.Value(n[j])
                cj    = solver.Value(sCj[j]) / SCALE
                total_workers += n_val
                print(f"  Group {j+1}: tasks={tasks}, workers={n_val}, Cj={cj:.4f}")
        print(f"\nTotal workers used: {total_workers}")
    else:
        print("No feasible solution found.")

def main():
    lines = [l.strip() for l in sys.stdin.read().splitlines() if l.strip()]
    M, N_hat, t, edges = parse_input(lines)
    print(f"Parsed: M={M}, N_hat={N_hat}, t={t}")
    print(f"Edges: {[(u+1,v+1) for u,v in edges]}")
    print(f"Parameters: Q={Q}, P={P}, SCALE={SCALE}")
    start = time.time()
    solve(M, N_hat, t, edges)
    print(f"\nRuntime: {time.time() - start:.4f} seconds")

if __name__ == "__main__":
    main()