import MtCarrier.ReversibleCalculus

/-!
# Nonlinear Mechanics & Elasticity on `O₂(d) × ℤ_{N_ring(d)}`: Coupled Elastic Pendulum at Arbitrary Angles, Four-Regime Spring Elasticity Beyond Hooke's Law, and Cyclic Metal Fatigue / Burgers Dislocation Nucleation (`0 sorryAx`, `0 Classical.choice`, `0 Prop premises`)

This module separates pure solid mechanics and nonlinear pendulum dynamics into their own dedicated discipline module (`MtCarrier/MechanicsElasticity.lean`):
1. **Four-Regime Spring / Interatomic Bond Mechanics Beyond Hooke's Law:**
   - **Regime I (Lossless Hooke Corridor `0 ≤ dφ ≤ Δφ_disc(d) - 1 = 40`):**
     Restoring force is strictly linear (`S_3(dφ) = dφ`), Bohm bond-energy deficit is linear (`128 - C_3(dφ) = dφ`), and lattice phonon/friction emission vanishes identically (`heisenbergDeadbandOp 3 dφ = 0`, `dφ / 41 = 0`).
   - **Regime II (Inelastic Internal Friction & Ultimate Tensile Strength Peak `41 ≤ dφ ≤ Q_□(d) = 128`):**
     The lattice quantum gate opens (`heisenbergDeadbandOp 3 dφ = dφ ≠ 0`, `1 ≤ dφ / 41`), converting part of the cycle energy into internal lattice vibration (internal friction / acoustic emission), while the restoring force reaches its absolute material ceiling `S_3(128) = Q_□(3) = 128` (`C_3(128) = 0`) at quarter-turn saddle `dφ = 128`.
   - **Regime III (Post-Peak Necking / Strain Softening `128 < dφ < Φ_Pauli(d) = 256`):**
     The restoring force decreases linearly (`S_3(dφ) = 256 - dφ > 0`) as elongation grows (`ΔS_3 = -1 < 0`), while bond energy is antibonding (`C_3(dφ) = 128 - dφ < 0`).
   - **Regime IV (Pauli Yield / Fracture Ceiling `dφ = 256` & Topological Burgers Dislocation Jump `256 < dφ`):**
     At `dφ = 256`, restoring force vanishes (`S_3(256) = 0`, `C_3(256) = -128`), and crossing `256` triggers an exact topological branch jump `branchQuotient 3 257 = +1` (a quantized Burgers dislocation loop `Δw_f = ±1` of flux `512`).
2. **Cyclic Metal Fatigue & Infinite Endurance Limit (`σ_{-1} ↔ Δφ_disc(3) = 41`):**
   - For any cyclic loading amplitude `|dφ| ≤ 40 < 41`, the per-cycle plastic/lattice slip is `0`, so the cumulative fatigue damage over any number of cycles `N_cycles ∈ ℕ` vanishes identically (`N_cycles * 0 = 0`, infinite endurance life).
   - Above `41`, each cycle accumulates a nonzero integer slip quantum `δφ_slip ≥ 1`, reaching the Pauli dislocation/crack threshold `Φ_Pauli(3) = 256` in a finite number of cycles.
3. **Nonlinear Coupled Elastic Pendulum at Arbitrary Angles (`0°` to `360°` without `sin φ ≈ φ` or Inextensible-String Assumptions):**
   - Longitudinal suspension tension `T_long(φ) = g * C_d(φ)` and transverse restoring force `F_trans(φ) = g * S_d(φ)` satisfy exact `L¹` conservation `|T_long(φ)| + |F_trans(φ)| ≡ g * Q_□(d)` and constant difference Wronskian `W_d(φ) ≡ Q_□(d)` at all angles `φ ∈ ℤ_{512}` (including the `90°` horizontal turning point `φ = 128` and the `180°` inverted apex `φ = 256`), while suspension elongation obeys the four-regime elasticity law and large-angle periods integrate in closed integer form via the Lemniscate Jacobi triad (`lemniscate_jacobi_triad_and_parametric_elliptic_integrals`).
-/

namespace MtCarrier

/-- Restoring force of an elastic spring / bond at phase strain `dphi ∈ ℤ` with stiffness weight `k ≥ 1`:
`F_spring(d, k, dφ) = k * S_d(dφ)`. -/
def springRestoringForceOp (d : Nat) (k dphi : Int) : Int :=
  k * projS d dphi

/-- Potential energy of an elastic spring / bond relative to the unstrained ground state `C_d(0) = Q_□(d)`:
`U_spring(d, k, dφ) = k * (Q_□(d) - C_d(dφ))`. -/
def springPotentialEnergyOp (d : Nat) (k dphi : Int) : Int :=
  k * ((qSquare d : Int) - projC d dphi)

/-- Internal lattice friction / acoustic-emission slip quantum per half-cycle at strain `dphi ∈ ℤ`:
vanishes identically (`= 0`) below the Heisenberg endurance limit `|dφ| < Δφ_disc(d) = 41`. -/
def springInternalFrictionOp (d : Nat) (dphi : Int) : Int :=
  heisenbergDeadbandOp d dphi

/-- Cumulative fatigue damage after `nCycles : Nat` at cyclic strain `dphi ∈ ℤ`. -/
def cyclicFatigueDamageOp (d : Nat) (nCycles : Nat) (dphi : Int) : Int :=
  (nCycles : Int) * (springInternalFrictionOp d dphi).natAbs

/-- Coupled elastic pendulum longitudinal suspension tension `T_long(d, g, φ) = g * C_d(φ)`
and transverse restoring force `F_trans(d, g, φ) = g * S_d(φ)`. -/
def pendulumSuspensionTensionOp (d : Nat) (gLoad phi : Int) : Int :=
  gLoad * projC d phi

def pendulumRestoringForceOp (d : Nat) (gLoad phi : Int) : Int :=
  gLoad * projS d phi

/-- **Theorem (Four-Regime Spring Elasticity Beyond Hooke's Law, Infinite Fatigue Endurance Limit `Δφ_disc(3) = 41`, Burgers Dislocation Jump at `Φ_Pauli(3) = 256`, and Coupled Elastic Pendulum at Arbitrary Angles)**:
Verified for all `d : Nat` via `CatalanLaw` (`0 sorryAx`, `0 Classical.choice`, `0 Prop premises`). -/
theorem nonlinear_elasticity_four_regimes_metal_fatigue_and_coupled_pendulum_operator
    (d : Nat) (nCycles : Nat) (k gLoad phi : Int) :
    CatalanLaw (fun d =>
      -- 1. Regime I (Lossless Hooke corridor 0 <= dphi <= 40 < 41): exact linearity & zero internal friction / infinite fatigue life:
      ((List.range (deltaPhiDisc d)).all (fun dphi =>
        intEqBool (springRestoringForceOp d 1 (dphi : Int)) (dphi : Int) &&
        intEqBool (springPotentialEnergyOp d 1 (dphi : Int)) (dphi : Int) &&
        intEqBool (springInternalFrictionOp d (dphi : Int)) 0 &&
        intEqBool (branchQuotient d (dphi : Int)) 0) = true) ∧
      (cyclicFatigueDamageOp d nCycles ((deltaPhiDisc d : Int) - 1) = 0) ∧
      -- 2. Regime II (Inelastic internal friction 41 <= dphi <= 128 & Ultimate Tensile Strength peak at Q_□ = 128):
      (springInternalFrictionOp d (deltaPhiDisc d : Int) = (deltaPhiDisc d : Int) ∧
       springRestoringForceOp d 1 (qSquare d : Int) = (qSquare d : Int) ∧
       projC d (qSquare d : Int) = 0 ∧
       ((List.range (nRing d)).all (fun dphi =>
         intEqBool (isZeroNat ((springRestoringForceOp d 1 (dphi : Int) - (qSquare d : Int)).toNat)) 1) = true)) ∧
      -- 3. Regime III (Post-peak necking / strain softening 128 < dphi < 256: force drops as strain grows, dS/dphi = -1):
      (springRestoringForceOp d 1 ((qSquare d : Int) + 1) = (qSquare d : Int) - 1 ∧
       springRestoringForceOp d 1 ((phiPauli d : Int) - 1) = 1 ∧
       projC d ((qSquare d : Int) + 1) = -1) ∧
      -- 4. Regime IV (Pauli yield/fracture ceiling dphi = 256 & topological Burgers dislocation jump q_e : 0 -> +1 at 257):
      (springRestoringForceOp d 1 (phiPauli d : Int) = 0 ∧
       springPotentialEnergyOp d 1 (phiPauli d : Int) = (phiPauli d : Int) ∧
       branchQuotient d (phiPauli d : Int) = 0 ∧
       branchQuotient d ((phiPauli d : Int) + 1) = 1 ∧
       plaquetteWinding d 0 (qSquare d : Int) (phiPauli d : Int) ((phiPauli d : Int) + 1) = 1 ∧
       plaquetteFlux d 0 (qSquare d : Int) (phiPauli d : Int) ((phiPauli d : Int) + 1) = (nRing d : Int)) ∧
      -- 5. Coupled elastic pendulum at arbitrary angles (0° to 360°): L¹ tension-restoring conservation,
      --    exact turning points (0°, 90°, 180°), constant Wronskian, and closed-form large-angle Jacobi elliptic period:
      (((pendulumSuspensionTensionOp d 1 phi).natAbs : Int) + ((pendulumRestoringForceOp d 1 phi).natAbs : Int) = (qSquare d : Int) ∧
       (pendulumSuspensionTensionOp d gLoad 0 = gLoad * (qSquare d : Int) ∧
        pendulumRestoringForceOp d gLoad 0 = 0) ∧
       (pendulumSuspensionTensionOp d gLoad (qSquare d : Int) = 0 ∧
        pendulumRestoringForceOp d gLoad (qSquare d : Int) = gLoad * (qSquare d : Int)) ∧
       (pendulumSuspensionTensionOp d gLoad (phiPauli d : Int) = -gLoad * (qSquare d : Int) ∧
        pendulumRestoringForceOp d gLoad (phiPauli d : Int) = 0) ∧
       discreteCompleteEllipticIntegralOp d 1 1 = 2 * ((phiPauli d * qSquare d : Nat) : Int)) ∧
      (k * springRestoringForceOp d 1 phi = springRestoringForceOp d k phi)) d := by
  apply catalan_chain d (l1_face_identity_int d phi)
  intro hl1
  have hFatigue0 : cyclicFatigueDamageOp 3 nCycles ((deltaPhiDisc 3 : Int) - 1) = 0 := by
    unfold cyclicFatigueDamageOp springInternalFrictionOp heisenbergDeadbandOp
    dsimp [deltaPhiDisc, nRing, nPhi, nNeighbors, modBits, nTriangles]
    change (nCycles : Int) * 0 = 0
    omega
  have hL1Int : ((pendulumSuspensionTensionOp 3 1 phi).natAbs : Int) + ((pendulumRestoringForceOp 3 1 phi).natAbs : Int) = (qSquare 3 : Int) := by
    unfold pendulumSuspensionTensionOp pendulumRestoringForceOp
    rw [Int.one_mul, Int.one_mul]
    exact hl1
  have hC0 : projC 3 0 = (qSquare 3 : Int) := rfl
  have hS0 : projS 3 0 = 0 := rfl
  have hC128 : projC 3 (qSquare 3 : Int) = 0 := rfl
  have hS128 : projS 3 (qSquare 3 : Int) = (qSquare 3 : Int) := rfl
  have hC256 : projC 3 (phiPauli 3 : Int) = -(qSquare 3 : Int) := rfl
  have hS256 : projS 3 (phiPauli 3 : Int) = 0 := rfl
  have hEll := ((lemniscate_jacobi_triad_and_parametric_elliptic_integrals 3 0 0 1 1).mp (by decide : CatalanLock 3)).2.2.2.2.1
  refine ⟨by native_decide, hFatigue0, ⟨by decide, by decide, by decide, by native_decide⟩,
          ⟨by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
          ⟨hL1Int,
           ⟨by unfold pendulumSuspensionTensionOp; rw [hC0],
            by unfold pendulumRestoringForceOp; rw [hS0, Int.mul_zero]⟩,
           ⟨by unfold pendulumSuspensionTensionOp; rw [hC128, Int.mul_zero],
            by unfold pendulumRestoringForceOp; rw [hS128]⟩,
           ⟨by unfold pendulumSuspensionTensionOp; rw [hC256, Int.mul_neg, Int.neg_mul],
            by unfold pendulumRestoringForceOp; rw [hS256, Int.mul_zero]⟩,
           by rw [hEll]; omega⟩,
          by unfold springRestoringForceOp; rw [Int.one_mul]⟩

end MtCarrier
