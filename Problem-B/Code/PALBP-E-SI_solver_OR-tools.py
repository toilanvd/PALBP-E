"""
Solve PALBP-E-SI using OR-Tools CP-SAT.
SI = sum((C - Cj)^2) primary, W*C^2 secondary.
Usage: python solve_ortools_si.py < input.txt
Global parameters Q=3, P=3.
"""

import sys
import math
import time
from ortools.sat.python import cp_model

Q = 3
P = 3
SCALE  = math.lcm(*range(1, Q + 1))   # 6
SCALE2 = SCALE * SCALE                  # 36 for SI
SCALE3 = SCALE * SCALE * SCALE         # 216 for W*C^2

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
    sSI_bar = W_max * sT_bar * sT_bar
    sLC_bar = W_max * sT_bar * sT_bar  # W * (SCALE*C)^2

    model = cp_model.CpModel()

    # x_ij: task i in group j
    x = {}
    for i in range(M):
        for j in range(W_max):
            x[i,j] = model.NewBoolVar(f"x_{i}_{j}")

    # z_jk: group j uses k workers
    z = {}
    for j in range(W_max):
        for k in range(1, Q+1):
            z[j,k] = model.NewBoolVar(f"z_{j}_{k}")

    # v_j: group j active
    v = [model.NewBoolVar(f"v_{j}") for j in range(W_max)]

    # (C1) each task in exactly one group
    for i in range(M):
        model.Add(sum(x[i,j] for j in range(W_max)) == 1)

    # (C2) x_ij <= v_j
    for i in range(M):
        for j in range(W_max):
            model.Add(x[i,j] <= v[j])

    # active[j] = OR(x[i,j])
    for j in range(W_max):
        model.AddBoolOr([x[i,j] for i in range(M)]).OnlyEnforceIf(v[j])
        model.AddBoolAnd([x[i,j].Not() for i in range(M)]).OnlyEnforceIf(v[j].Not())

    # (C3) precedence
    for (ut, vt) in edges:
        for j in range(W_max):
            model.Add(
                sum(x[ut,j_] for j_ in range(j+1)) >=
                sum(x[vt,j_] for j_ in range(j+1))
            )

    # (C4) max P tasks per group
    for j in range(W_max):
        model.Add(sum(x[i,j] for i in range(M)) <= P * v[j])

    # (C5) exactly one k per active group
    for j in range(W_max):
        model.Add(sum(z[j,k] for k in range(1,Q+1)) == v[j])

    # (C6) total workers
    if N_hat < 10**7:
        model.Add(sum(k * z[j,k] for j in range(W_max) for k in range(1,Q+1)) <= N_hat)

    # T_j = sum t_i * x_ij (unscaled)
    Tj = [model.NewIntVar(0, T_bar, f"T_{j}") for j in range(W_max)]
    for j in range(W_max):
        model.Add(Tj[j] == sum(t[i] * x[i,j] for i in range(M)))

    # (C7) T_jk = T_j * z_jk via McCormick
    Tjk = {}
    for j in range(W_max):
        for k in range(1, Q+1):
            Tjk[j,k] = model.NewIntVar(0, T_bar, f"Tjk_{j}_{k}")
            model.Add(Tjk[j,k] <= T_bar * z[j,k])
            model.Add(Tjk[j,k] <= Tj[j])
            model.Add(Tjk[j,k] >= Tj[j] - T_bar * (1 - z[j,k]))

    # sCj = SCALE * Cj = SCALE * T_j / n_j
    # When n_j = k: sCj * k = SCALE * T_jk (since T_jk = T_j when z_jk=1)
    sCj = [model.NewIntVar(0, sT_bar, f"sCj_{j}") for j in range(W_max)]
    for j in range(W_max):
        model.Add(sCj[j] == 0).OnlyEnforceIf(v[j].Not())
        for k in range(1, Q+1):
            model.Add(sCj[j] * k == SCALE * Tjk[j,k]).OnlyEnforceIf(z[j,k])

    # sC = SCALE * C = max(sCj); minimization drives sC = max
    sC = model.NewIntVar(0, sT_bar, "sC")
    for j in range(W_max):
        model.Add(sC >= sCj[j])

    # (C9) symmetry breaking
    for j in range(W_max - 1):
        model.Add(v[j] >= v[j+1])

    # W = sum(v_j)
    W_var = model.NewIntVar(0, W_max, "W")
    model.Add(W_var == sum(v))

    # sSI = sum over active j of (sC - sCj)^2
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

    sSI = model.NewIntVar(0, sSI_bar, "sSI")
    model.Add(sSI == sum(sSI_terms))

    # Secondary: W * C^2  =>  scaled: W * sC^2
    sC2 = model.NewIntVar(0, sT_bar * sT_bar, "sC2")
    model.AddMultiplicationEquality(sC2, [sC, sC])

    sLC = model.NewIntVar(0, W_max * sT_bar * sT_bar, "sLC")
    model.AddMultiplicationEquality(sLC, [W_var, sC2])

    # Lexicographic: min sSI then sLC
    BIG = W_max * sT_bar * sT_bar + 1
    model.Minimize(sSI * BIG + sLC)

    # Progress callback
    class ProgressCallback(cp_model.CpSolverSolutionCallback):
        def __init__(self):
            cp_model.CpSolverSolutionCallback.__init__(self)
            self._best = float('inf')
            self._count = 0
            self._start = time.time()

        def on_solution_callback(self):
            self._count += 1
            si_val = self.Value(sSI) / SCALE2
            lc_val = self.Value(sLC) / SCALE2
            elapsed = time.time() - self._start
            if si_val < self._best:
                self._best = si_val
                bar_len = 40
                max_si = W_max * (T_bar) ** 2
                fill = int(bar_len * max(0, 1 - si_val / max_si)) if max_si > 0 else 0
                bar = '#' * fill + '-' * (bar_len - fill)
                print(f"\r  [{bar}] sol#{self._count:>3d} | SI={si_val:.4f}  W*C²={lc_val:.4f}  t={elapsed:.2f}s",
                      end='', flush=True)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 43200.0
    solver.parameters.num_search_workers = 24
    cb = ProgressCallback()
    print("Solving...")
    status = solver.Solve(model, cb)
    print()

    print(f"\nStatus: {solver.StatusName(status)}")
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sC_val  = solver.Value(sC)
        W_val   = solver.Value(W_var)
        sSI_val = solver.Value(sSI)
        sLC_val = solver.Value(sLC)
        C_val   = sC_val / SCALE
        SI_val  = sSI_val / SCALE2
        LC_val  = sLC_val / SCALE2
        print(f"C          = {C_val:.4f}")
        print(f"W          = {W_val}")
        print(f"SI         = {SI_val:.4f}")
        print(f"W*C²       = {LC_val:.4f}")
        print(f"Optimal    = {status == cp_model.OPTIMAL}")
        print("\nGroup assignments:")
        total_workers = 0
        for j in range(W_max):
            if solver.Value(v[j]) == 1:
                tasks  = [i+1 for i in range(M) if solver.Value(x[i,j]) == 1]
                n_val  = next(k for k in range(1,Q+1) if solver.Value(z[j,k]) == 1)
                cj_val = solver.Value(sCj[j]) / SCALE
                total_workers += n_val
                print(f"  Group {j+1}: tasks={tasks}, workers={n_val}, Cj={cj_val:.4f}")
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