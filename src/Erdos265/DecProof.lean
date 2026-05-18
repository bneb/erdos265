import Mathlib

open Filter Topology Real BigOperators Finset

-- Let S_N = sum_{k \ge N} 1/X_k
-- C_N = P_N S_N.
-- We want to show C_{N+1} < C_N eventually.
-- C_{N+1} = P_{N+1} S_{N+1} = P_N X_N (S_N - 1/X_N) = X_N C_N - P_N.
-- C_{N+1} < C_N  <=>  X_N C_N - P_N < C_N  <=>  (X_N - 1) C_N < P_N
-- <=> C_N < P_N / (X_N - 1)  <=>  P_N S_N < P_N / (X_N - 1)
-- <=> S_N < 1 / (X_N - 1).

-- But S_N = 1/X_N + S_{N+1}.
-- So S_N < 1 / (X_N - 1)  <=>  1/X_N + S_{N+1} < 1 / (X_N - 1)
-- <=> S_{N+1} < 1 / (X_N - 1) - 1/X_N
-- <=> S_{N+1} < 1 / (X_N (X_N - 1)).

-- Therefore, C_{N+1} < C_N if and only if S_{N+1} < 1 / (X_N (X_N - 1)).
