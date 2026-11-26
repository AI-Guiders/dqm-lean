import MtCarrier.TrajectoryIV263

/-!
# Bridge Executable `mt_carrier_dump`: Lean 4 ↔ Python (`mt_ca/carrier_core.py`) JSON Diff

Exports a deterministic JSON payload computed directly by the Lean 4 kernel/runtime:
1. `CarrierSpec.from_d(3)` invariants (`mod_bits`, `frac_bits`, `n_ring`, `k_p`, `k_p_sq`, `q_square`, `phi_pauli`, `n_neighbors`, `n_phi`, `n_triangles`, `n_squares`, `dphi_min_ticks`, `m_hat`, `iv_9bit`).
2. Full 512-entry face projection tables `C(A)` and `S(A)` (`ring_face_lut_core`).
3. Full 512-entry integer Pythagorean triples `(P_x(A), P_y(A), P_r(A))`.
4. Exact 3D `IV(3) = 263` trajectory census at `t = 0, 1, 2`:
   - `active_t0 = 543`, `active_t1 = 578`,
   - `vortex_xy_t2 = 26`, `vortex_yz_t2 = 26`, `vortex_xz_t2 = 34`, `vortex_total_t2 = 86`,
   - `max_cube_div_t2 = 0`,
   - central `K₃` plaquette corners at `t = 0, 1, 2`.

This executable is invoked by `verify_checks/` to diff Lean 4's formal definitions
bit-for-bit against `mt_ca/carrier_core.py`.
-/

open MtCarrier

def intListToJson (xs : List Int) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

def main : IO Unit := do
  let cLut := (List.range (nRing 3)).map (fun (n : Nat) => projC 3 (Int.ofNat n))
  let sLut := (List.range (nRing 3)).map (fun (n : Nat) => projS 3 (Int.ofNat n))
  let pxLut := (List.range (nRing 3)).map (fun (n : Nat) => pythPx 3 (Int.ofNat n))
  let pyLut := (List.range (nRing 3)).map (fun (n : Nat) => pythPy 3 (Int.ofNat n))
  let prLut := (List.range (nRing 3)).map (fun (n : Nat) => pythPr 3 (Int.ofNat n))
  let (act0, act1, nxy, nyz, nxz, maxDiv) := runFull3DCensusIV263 3
  let json :=
    "{\n" ++
    s!"  \"d\": 3,\n" ++
    s!"  \"n_neighbors\": {nNeighbors 3},\n" ++
    s!"  \"n_phi\": {nPhi 3},\n" ++
    s!"  \"n_triangles\": {nTriangles 3},\n" ++
    s!"  \"n_squares\": {nSquares 3},\n" ++
    s!"  \"d_in_square\": {dInSquare},\n" ++
    s!"  \"mod_bits\": {modBits 3},\n" ++
    s!"  \"n_ring\": {nRing 3},\n" ++
    s!"  \"frac_bits\": {fracBits 3},\n" ++
    s!"  \"k_p\": {kP 3},\n" ++
    s!"  \"k_p_sq\": {(kP 3) ^ 2},\n" ++
    s!"  \"q_square\": {qSquare 3},\n" ++
    s!"  \"phi_pauli\": {phiPauli 3},\n" ++
    s!"  \"dphi_min_ticks\": {(nRing 3 + nPhi 3 + nTriangles 3) / nPhi 3},\n" ++
    s!"  \"m_hat\": {mHat 3},\n" ++
    s!"  \"iv_9bit\": {ivSeed 3},\n" ++
    s!"  \"c_lut\": {intListToJson cLut},\n" ++
    s!"  \"s_lut\": {intListToJson sLut},\n" ++
    s!"  \"px_lut\": {intListToJson pxLut},\n" ++
    s!"  \"py_lut\": {intListToJson pyLut},\n" ++
    s!"  \"pr_lut\": {intListToJson prLut},\n" ++
    s!"  \"iv263_active_t0\": {act0},\n" ++
    s!"  \"iv263_active_t1\": {act1},\n" ++
    s!"  \"iv263_vortex_xy_t2\": {nxy},\n" ++
    s!"  \"iv263_vortex_yz_t2\": {nyz},\n" ++
    s!"  \"iv263_vortex_xz_t2\": {nxz},\n" ++
    s!"  \"iv263_vortex_total_t2\": {nxy + nyz + nxz},\n" ++
    s!"  \"iv263_max_cube_div_t2\": {maxDiv}\n" ++
    "}"
  IO.println json
