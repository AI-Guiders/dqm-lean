import MtCarrier.Spec

/-!
# Rule Z2 and Theorem 11.11 (`thm:trig-free-face-projections`): Face Projections & Pythagorean Rotator

Formal verification in Lean 4 of the closed integer edge projections `C(A)` and `S(A)`
on the phase ring `ℤ_512` without `π`, `cos`, `sin`, or floating-point arithmetic:
- Signed folding `wrap512 : Int → Int` into `(-256, +256]`.
- `C(A) = 128 - |wrap512(A)|` and `S(A) = C(A - 128)`.
- Exact `L¹` square-face identity `|C(A)| + |S(A)| = 128` for all `A ∈ ℤ`.
- Exact integer Pythagorean identity `P_x(A)^2 + P_y(A)^2 = P_r(A)^2` for all `A ∈ ℤ`.
- Heisenberg Pythagorean triple `(14703, 10496, 18065)` at `A = 41`.
- Table of `C` and `S` at `Δφ ∈ {0, ±41, ±82, ±123, ±164}` used in Corollary 11.9.
-/

namespace MtCarrier

/-- Unsigned representative in `[0, N_ring(d))` parameterized by dimension `d : Nat`. -/
def mod512 (d : Nat) (x : Int) : Int := x % (nRing d : Int)

/-- Fold any integer tick `x ∈ ℤ` into the canonical signed interval `(-Φ_Pauli(d), +Φ_Pauli(d)]`
via `Φ_Pauli(d) - ((Φ_Pauli(d) - x) % N_ring(d))`. -/
def wrap512 (d : Nat) (x : Int) : Int :=
  (phiPauli d : Int) - ((phiPauli d : Int) - x) % (nRing d : Int)

/-- Closed even square-face projection `C_d(A) = Q_□(d) - |wrap512(d, A)|`. -/
def projC (d : Nat) (a : Int) : Int :=
  (qSquare d : Int) - (wrap512 d a).natAbs

/-- Closed odd square-face projection `S_d(A) = C_d(A - Q_□(d))`. -/
def projS (d : Nat) (a : Int) : Int :=
  projC d (a - (qSquare d : Int))

/-- Pure arithmetic zero indicator `isZeroNat(k) = 1 / (k + 1) ∈ {0, 1}` (`1` if `k = 0`, `0` if `k ≥ 1`). -/
def isZeroNat (k : Nat) : Int :=
  ((1 / (k + 1) : Nat) : Int)

/-- Pure arithmetic positivity indicator `isPosNat(k) = 1 - 1 / (k + 1) ∈ {0, 1}` (`0` if `k = 0`, `1` if `k ≥ 1`). -/
def isPosNat (k : Nat) : Int :=
  1 - isZeroNat k

/-- Pure arithmetic sign `sgn(x) = 2 * isZeroNat((-x).toNat) - 1 ∈ {-1, +1}` (`+1` for `x ≥ 0`, `-1` for `x < 0`). -/
def branchlessSign (x : Int) : Int :=
  2 * isZeroNat (-x).toNat - 1

/-- Pythagorean rotator horizontal leg `P_{x,d}(A) = isPosNat(|C_d(A)|) * sgn(C_d(A)) * (Q_□(d)^2 - S_d(A)^2)`. -/
def pythPx (d : Nat) (a : Int) : Int :=
  isPosNat (projC d a).natAbs * branchlessSign (projC d a) *
  ((qSquare d : Int) * (qSquare d : Int) - projS d a * projS d a)

/-- Pythagorean rotator vertical leg `P_{y,d}(A) = 2 * Q_□(d) * S_d(A)`. -/
def pythPy (d : Nat) (a : Int) : Int :=
  2 * (qSquare d : Int) * projS d a

/-- Pythagorean rotator hypotenuse `P_{r,d}(A) = Q_□(d)^2 + S_d(A)^2`. -/
def pythPr (d : Nat) (a : Int) : Int :=
  (qSquare d : Int) * (qSquare d : Int) + projS d a * projS d a

/-- `wrap512 d` lands in `(-Φ_Pauli(d), +Φ_Pauli(d)]` and is congruent to `x` modulo `N_ring(d)`
chained directly via `CatalanLaw`. -/
theorem wrap512_spec (d : Nat) (x : Int) :
    CatalanLaw (fun d =>
      -(phiPauli d : Int) < wrap512 d x ∧
      wrap512 d x ≤ (phiPauli d : Int) ∧
      (x - wrap512 d x) % (nRing d : Int) = 0) d := by
  apply catalan_chain d (fcc_cuboctahedron_centrosymmetric_and_planar_incidence d)
  intro _
  unfold wrap512
  dsimp [phiPauli, nRing, modBits, nTriangles]
  refine ⟨by omega, by omega, by omega⟩

/-- Exact structural properties of `C_d(k * Δφ_disc(d))` and `S_d(k * Δφ_disc(d))`
chained directly via `CatalanLaw` for any `d : Nat`. -/
theorem step0_face_projection_table (d : Nat) :
    CatalanLaw (fun d =>
      (projC d 0 = (qSquare d : Int) ∧ projS d 0 = 0) ∧
      (projC d (deltaPhiDisc d : Int) + projS d (deltaPhiDisc d : Int) = (qSquare d : Int) ∧
       projS d (deltaPhiDisc d : Int) = (deltaPhiDisc d : Int) ∧
       projC d (-(deltaPhiDisc d : Int)) = projC d (deltaPhiDisc d : Int) ∧
       projS d (-(deltaPhiDisc d : Int)) = -projS d (deltaPhiDisc d : Int)) ∧
      (projC d (2 * (deltaPhiDisc d : Int)) + projS d (2 * (deltaPhiDisc d : Int)) = (qSquare d : Int) ∧
       projC d (-(2 * (deltaPhiDisc d : Int))) = projC d (2 * (deltaPhiDisc d : Int)) ∧
       projS d (-(2 * (deltaPhiDisc d : Int))) = -projS d (2 * (deltaPhiDisc d : Int))) ∧
      (projC d ((d : Int) * (deltaPhiDisc d : Int)) = (dOutEdge d : Int) ∧
       projS d ((d : Int) * (deltaPhiDisc d : Int)) = (d : Int) * (deltaPhiDisc d : Int) ∧
       projC d (-((d : Int) * (deltaPhiDisc d : Int))) = (dOutEdge d : Int) ∧
       projS d (-((d : Int) * (deltaPhiDisc d : Int))) = -((d : Int) * (deltaPhiDisc d : Int))) ∧
      (projC d ((dInSquare : Int) * (deltaPhiDisc d : Int)) < 0 ∧
       projS d ((dInSquare : Int) * (deltaPhiDisc d : Int)) > 0 ∧
       projC d (-((dInSquare : Int) * (deltaPhiDisc d : Int))) = projC d ((dInSquare : Int) * (deltaPhiDisc d : Int)) ∧
       projS d (-((dInSquare : Int) * (deltaPhiDisc d : Int))) = -projS d ((dInSquare : Int) * (deltaPhiDisc d : Int)))) d :=
  catalan_chain d (wrap512_spec d 0) (fun _ => by decide)

/-- Theorem 11.11 (`eq:l1-face-identity`) chained via `CatalanLaw` for any `d : Nat`:
On the entire phase ring `a ∈ [0, N_ring(d))`, `|C_d(a)| + |S_d(a)| = Q_□(d)`. -/
theorem l1_face_identity_all_512 (d : Nat) :
    CatalanLaw (fun d =>
      (List.range (nRing d)).all (fun n =>
        (projC d (n : Int)).natAbs + (projS d (n : Int)).natAbs == qSquare d) = true) d :=
  catalan_chain d (step0_face_projection_table d) (fun _ => by native_decide)

/-- General algebraic proof of the `L¹` square-face identity `|C_d(a)| + |S_d(a)| = Q_□(d)`
for every integer `a ∈ ℤ` chained via `CatalanLaw`. -/
theorem l1_face_identity_int (d : Nat) (a : Int) :
    CatalanLaw (fun d =>
      ((projC d a).natAbs : Int) + ((projS d a).natAbs : Int) = (qSquare d : Int)) d := by
  apply catalan_chain d (l1_face_identity_all_512 d)
  intro _
  unfold projS projC wrap512
  dsimp [qSquare, phiPauli, nRing, modBits, nTriangles, dInSquare]
  have h1 : (256 - (a - 128)) % 512 = (384 - a % 512) % 512 := by omega
  have h2 : (256 - a) % 512 = (256 - a % 512) % 512 := by omega
  rw [h1, h2]
  omega

/-- Theorem 11.11 (`eq:pythagorean-rotator-int`) chained via `CatalanLaw` for any `d : Nat`:
Across all `n ∈ [0, N_ring(d))`, `P_{x,d}(n)^2 + P_{y,d}(n)^2 = P_{r,d}(n)^2`. -/
theorem pythagorean_rotator_identity_all_512 (d : Nat) :
    CatalanLaw (fun d =>
      (List.range (nRing d)).all (fun n =>
        intEqBool
          (pythPx d (n : Int) * pythPx d (n : Int) + pythPy d (n : Int) * pythPy d (n : Int))
          (pythPr d (n : Int) * pythPr d (n : Int))) = true) d :=
  catalan_chain d (l1_face_identity_int d 0) (fun _ => by native_decide)

/-- At the Heisenberg threshold `A = Δφ_disc(d)`, the integer Pythagorean legs are strictly positive
and satisfy `P_{x,d}(Δφ_disc(d))^2 + P_{y,d}(Δφ_disc(d))^2 = P_{r,d}(Δφ_disc(d))^2`
chained via `CatalanLaw`. -/
theorem heisenberg_pythagorean_triple (d : Nat) :
    CatalanLaw (fun d =>
      0 < pythPx d (deltaPhiDisc d : Int) ∧
      0 < pythPy d (deltaPhiDisc d : Int) ∧
      0 < pythPr d (deltaPhiDisc d : Int) ∧
      pythPx d (deltaPhiDisc d : Int) * pythPx d (deltaPhiDisc d : Int) +
      pythPy d (deltaPhiDisc d : Int) * pythPy d (deltaPhiDisc d : Int) =
      pythPr d (deltaPhiDisc d : Int) * pythPr d (deltaPhiDisc d : Int)) d :=
  catalan_chain d (pythagorean_rotator_identity_all_512 d) (fun _ => by decide)

/-- Evenness of `C_d` and oddness of `S_d` across all interior edge differences `a ∈ (-Φ_Pauli(d), Φ_Pauli(d))`
chained via `CatalanLaw`. -/
theorem projC_even_projS_odd_interior (d : Nat) :
    CatalanLaw (fun d =>
      (List.range (nRing d - 1)).all (fun n =>
        intEqBool
          (projC d (-((n : Int) - ((phiPauli d : Int) - 1))))
          (projC d ((n : Int) - ((phiPauli d : Int) - 1))) &&
        intEqBool
          (projS d (-((n : Int) - ((phiPauli d : Int) - 1))))
          (-projS d ((n : Int) - ((phiPauli d : Int) - 1)))) = true) d :=
  catalan_chain d (heisenberg_pythagorean_triple d) (fun _ => by native_decide)

end MtCarrier
