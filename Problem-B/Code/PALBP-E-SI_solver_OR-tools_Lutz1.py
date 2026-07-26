"""
Solve PALBP-E-SI using OR-Tools CP-SAT.
SI = sum((C - Cj)^2 * v_j) primary, W*C^2 secondary.
Uses two-phase solving to avoid int64 overflow in lexicographic objective.
Usage: python solve_ortools_si.py < input.txt
Global parameters Q=3, P=3.
"""

import sys
import math
import time
from ortools.sat.python import cp_model

Q = 3
P = 3
SCALE  = math.lcm(*range(1, Q + 1))  # 6
SCALE2 = SCALE * SCALE                 # 36

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

def build_model(M, N_hat, t, edges, T_bar, W_max, sT_bar):
    """Build the CP-SAT model and return model + key variables."""
    model = cp_model.CpModel()

    x = {(i,j): model.NewBoolVar(f"x_{i}_{j}")
         for i in range(M) for j in range(W_max)}
    z = {(j,k): model.NewBoolVar(f"z_{j}_{k}")
         for j in range(W_max) for k in range(1, Q+1)}
    v = [model.NewBoolVar(f"v_{j}") for j in range(W_max)]

    # (1) each task in exactly one group
    for i in range(M):
        model.Add(sum(x[i,j] for j in range(W_max)) == 1)

    # (2) x_ij <= v_j; active iff any task assigned
    for j in range(W_max):
        for i in range(M):
            model.Add(x[i,j] <= v[j])
        model.AddBoolOr([x[i,j] for i in range(M)]).OnlyEnforceIf(v[j])
        model.AddBoolAnd([x[i,j].Not() for i in range(M)]).OnlyEnforceIf(v[j].Not())

    # (3) max P tasks per group
    for j in range(W_max):
        model.Add(sum(x[i,j] for i in range(M)) <= P * v[j])

    # (4) precedence
    for (ut, vt) in edges:
        for j in range(W_max):
            model.Add(sum(x[ut,j_] for j_ in range(j+1)) >=
                      sum(x[vt,j_] for j_ in range(j+1)))

    # (5) T_j
    Tj = [model.NewIntVar(0, T_bar, f"T_{j}") for j in range(W_max)]
    for j in range(W_max):
        model.Add(Tj[j] == sum(t[i]*x[i,j] for i in range(M)))

    # (6) one k per active group
    for j in range(W_max):
        model.Add(sum(z[j,k] for k in range(1,Q+1)) == v[j])

    # (7) worker budget
    if N_hat < 10**7:
        model.Add(sum(k*z[j,k] for j in range(W_max) for k in range(1,Q+1)) <= N_hat)

    # (8) McCormick T_jk = T_j * z_jk
    Tjk = {(j,k): model.NewIntVar(0, T_bar, f"Tjk_{j}_{k}")
           for j in range(W_max) for k in range(1,Q+1)}
    for j in range(W_max):
        for k in range(1, Q+1):
            model.Add(Tjk[j,k] <= T_bar * z[j,k])
            model.Add(Tjk[j,k] <= Tj[j])
            model.Add(Tjk[j,k] >= Tj[j] - T_bar*(1-z[j,k]))

    # (9) sCj = SCALE * Cj
    sCj = [model.NewIntVar(0, sT_bar, f"sCj_{j}") for j in range(W_max)]
    for j in range(W_max):
        model.Add(sCj[j] == 0).OnlyEnforceIf(v[j].Not())
        for k in range(1, Q+1):
            model.Add(sCj[j]*k == SCALE*Tjk[j,k]).OnlyEnforceIf(z[j,k])

    # (10) sC = max(sCj)
    sC = model.NewIntVar(0, sT_bar, "sC")
    for j in range(W_max):
        model.Add(sC >= sCj[j])

    # (11) symmetry breaking
    for j in range(W_max-1):
        model.Add(v[j] >= v[j+1])

    W_var = model.NewIntVar(0, W_max, "W")
    model.Add(W_var == sum(v))

    # SI terms: diff_j, diff2_j, si_j
    sSI_terms = []
    for j in range(W_max):
        diff = model.NewIntVar(-sT_bar, sT_bar, f"diff_{j}")
        model.Add(diff == sC - sCj[j])
        diff2 = model.NewIntVar(0, sT_bar * sT_bar, f"diff2_{j}")
        model.AddMultiplicationEquality(diff2, [diff, diff])
        si_j = model.NewIntVar(0, sT_bar * sT_bar, f"si_{j}")
        model.Add(si_j == diff2).OnlyEnforceIf(v[j])
        model.Add(si_j == 0).OnlyEnforceIf(v[j].Not())
        sSI_terms.append(si_j)

    sSI = model.NewIntVar(0, W_max * sT_bar * sT_bar, "sSI")
    model.Add(sSI == sum(sSI_terms))

    # W*C^2: sC2 = sC^2, sLC = W * sC2
    sC2 = model.NewIntVar(0, sT_bar * sT_bar, "sC2")
    model.AddMultiplicationEquality(sC2, [sC, sC])
    sLC = model.NewIntVar(0, W_max * sT_bar * sT_bar, "sLC")
    model.AddMultiplicationEquality(sLC, [W_var, sC2])

    return model, x, v, z, sCj, sC, W_var, sSI, sLC

def solve(M, N_hat, t, edges):
    T_bar  = sum(t)
    W_max  = M
    sT_bar = SCALE * T_bar

    print(f"T_bar={T_bar}, sT_bar={sT_bar}, sT_bar^2={sT_bar**2:.2e}")

    # ---- Phase 1: minimize sSI ----
    print("\nPhase 1: minimizing SI...")
    model1, x, v, z, sCj, sC, W_var, sSI, sLC = build_model(
        M, N_hat, t, edges, T_bar, W_max, sT_bar)
    model1.Minimize(sSI)

    class Phase1CB(cp_model.CpSolverSolutionCallback):
        def __init__(self):
            cp_model.CpSolverSolutionCallback.__init__(self)
            self._best = float('inf')
            self._start = time.time()
            self._count = 0
        def on_solution_callback(self):
            self._count += 1
            si = self.Value(sSI) / SCALE2
            if si < self._best:
                self._best = si
                bar = '#' * int(40 * max(0, 1 - si/(W_max*T_bar**2))) + '-' * 40
                bar = bar[:40]
                print(f"\r  [{bar}] sol#{self._count:>3d} | SI={si:.4f}  t={time.time()-self._start:.2f}s",
                      end='', flush=True)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 3600.0
    solver.parameters.num_search_workers = 8
    cb1 = Phase1CB()
    status1 = solver.Solve(model1, cb1)
    print()

    if status1 not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        print("Phase 1: No solution found.")
        return

    sSI_opt = solver.Value(sSI)
    SI_opt  = sSI_opt / SCALE2
    print(f"Phase 1 {solver.StatusName(status1)}: SI = {SI_opt:.4f}")

    # ---- Phase 2: fix sSI, minimize W*C^2 ----
    print("\nPhase 2: minimizing W*C² with SI fixed...")
    model2, x2, v2, z2, sCj2, sC2, W_var2, sSI2, sLC2 = build_model(
        M, N_hat, t, edges, T_bar, W_max, sT_bar)
    model2.Add(sSI2 == sSI_opt)
    model2.Minimize(sLC2)

    class Phase2CB(cp_model.CpSolverSolutionCallback):
        def __init__(self):
            cp_model.CpSolverSolutionCallback.__init__(self)
            self._best = float('inf')
            self._start = time.time()
            self._count = 0
        def on_solution_callback(self):
            self._count += 1
            lc = self.Value(sLC2) / SCALE2
            if lc < self._best:
                self._best = lc
                print(f"\r  sol#{self._count:>3d} | W*C²={lc:.4f}  t={time.time()-self._start:.2f}s",
                      end='', flush=True)

    solver2 = cp_model.CpSolver()
    solver2.parameters.max_time_in_seconds = 43200.0
    solver2.parameters.num_search_workers = 24
    cb2 = Phase2CB()
    status2 = solver2.Solve(model2, cb2)
    print()

    print(f"\nPhase 2 {solver2.StatusName(status2)}")
    if status2 in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sC_val  = solver2.Value(sC2)
        W_val   = solver2.Value(W_var2)
        sLC_val = solver2.Value(sLC2)
        C_val   = sC_val / SCALE
        LC_val  = sLC_val / SCALE2
        print(f"\nFinal solution:")
        print(f"C          = {C_val:.4f}")
        print(f"W          = {W_val}")
        print(f"SI         = {SI_opt:.4f}")
        print(f"W*C²       = {LC_val:.4f}")
        print(f"Phase 1    = {solver.StatusName(status1)}")
        print(f"Phase 2    = {solver2.StatusName(status2)}")
        print("\nGroup assignments:")
        total_workers = 0
        for j in range(W_max):
            if solver2.Value(v2[j]) == 1:
                tasks = [i+1 for i in range(M) if solver2.Value(x2[i,j]) == 1]
                n_val = next(k for k in range(1,Q+1) if solver2.Value(z2[j,k]) == 1)
                cj    = solver2.Value(sCj2[j]) / SCALE
                total_workers += n_val
                print(f"  Group {j+1}: tasks={tasks}, workers={n_val}, Cj={cj:.4f}")
        print(f"\nTotal workers used: {total_workers}")
    else:
        print("Phase 2: No solution found.")

def main():
    lines = [l.strip() for l in sys.stdin.read().splitlines() if l.strip()]
    M, N_hat, t, edges = parse_input(lines)
    print(f"Parsed: M={M}, N_hat={N_hat}")
    print(f"t = {t}")
    print(f"Edges: {len(edges)} precedence constraints")
    print(f"Parameters: Q={Q}, P={P}, SCALE={SCALE}")
    start = time.time()
    solve(M, N_hat, t, edges)
    print(f"\nTotal runtime: {time.time()-start:.4f} seconds")

if __name__ == "__main__":
    main()