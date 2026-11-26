# DQM Lean 4 Formalization (`AI-Guiders/dqm-lean`)

**Two-Contour Formal Verification Architecture: Pure Constructive Core (`0 Classical.choice`, `0 sorryAx`) & Standard `mathlib4` Bridge**

**Author:** Dmitrii A. Karataev (Д. А. Каратаев)  
**Formal Verification Partner:** Luch (Луч, AI-Guiders)  
**License:** GPL-3.0-or-later / CC-BY-SA-4.0

---

## Why Two Separate Contours?

Standard `mathlib4` relies pervasively on the non-constructive axiom of choice (`Classical.choice`) even for basic real/complex division. Mixing our constructive integer and projective proofs directly into a `mathlib4`-dependent root package would pollute `#print axioms` with `Classical.choice` and obscure the constructive foundation.

Therefore, this repository is cleanly separated into **two contours**:

### 1. Contour 1 — Pure Constructive Core (Root `lakefile.lean`: `Constructive/` & `MtCarrier/`)
- **Zero external dependencies** (pure Lean 4 core), **`0 sorryAx`**, **`0 Classical.choice`** (verified by `MtCarrier/AxiomAudit.lean` via `#print axioms`, depending only on `[propext, Quot.sound]`).
- **`Constructive/` (Pure Constructive Mathematics over $\mathbb{Z}_{2^m} \to \mathbb{P}^1(\mathbb{Q})$):**
  1. `RotatorQuadrature.lean` — Discrete Euler exponential on $\mathbb{Z}_{512}$ & $\mathbb{Z}_{4Q}$, constant difference Wronskian $W \equiv Q$, Weierstrass stereographic lift to $S^1(\mathbb{Q})$, and closed-form Fresnel, Jacobi, Dirichlet, Parseval, and Bessel quadrature.
  2. `LogicCohomology.lean` — Post functional completeness (`NOT, XOR, OR, AND`), 3-SAT phase reduction, constructive de Rham–Stokes–Gauss–Chern cohomology ($d^2 \equiv 0$), and finite-state adversary barriers.
  3. `PillaiDiophantine.lean` — Stage-partition matrix transmissions on the Minkowski light cone, parabolic $\mathrm{SL}_2(\mathbb{Z})$ Jordan locks, and $M$-floor Padé–Thue gear cascades.
  4. `AbcPlanetaryWronskian.lean` — Three-shaft planetary differentials $A + B = C$, Bézout–Padé Wronskians, and cross-floor locks.
  5. `ModelTheoreticLimit.lean` — Mal'cev algebraic systems, projective tower stabilization $\lim M_n = \mathcal{M}$, kernel annihilation $\ker\pi \subseteq \ker d_1 \cap \ker d_2$, and the polymorphic Lawvere–Gödel–Tarski diagonal theorem.
  6. `CollatzPlanetarySplice.lean` — Two-screw planetary gear cascades, Willis balance, and $S_b$ stage-permutation squeeze.
  7. `RiemannHolonomy.lean` — Projective Cayley–Weierstrass equator ($\mathrm{Re}(s) = 1/2 \iff |w(s)| = 1$), two-wave destructive interference in Pauli antiphase $\pi$, Parseval energy conservation, Cauchy–Riemann frequency-Wronskian radial growth identity $\mathcal{W}_t(U, V) = \frac{1}{2}\partial_\delta|\xi|^2$, Hadamard paired counter-zero retrograde lock, and unconditional multi-stage Minkowski–$\mathrm{SL}_2(\mathbb{Z})$ cascade zero lock.
- **`MtCarrier/` (31 Modules of Constructive Discrete Quantum Mechanics on $O_2(3) \times \mathbb{Z}_{512}$):**
  - `Spec.lean`, `FaceAlgebra.lean`, `HolonomyMaxwell.lean`, `TrajectoryIV263.lean`, `ContinuumPhysics.lean`, `NuclearShells.lean`, `ParticleMaterials.lean`, `BioCosmology.lean`, `ReversibleCalculus.lean`, `HardwarePhotovoltaics.lean`, `UnifiedOperators.lean`, `AxiomAudit.lean`, etc.

```bash
# Build Contour 1 (pure constructive core, builds in seconds with zero external downloads):
lake build
```

### 2. Contour 2 — Standard `mathlib4` Bridge (`MathlibBridge/`)
- Separate Lake package (`MathlibBridge/lakefile.lean`) that requires `leanprover-community/mathlib4` and imports `Constructive/`.
- Designed for classical mathematicians and the Lean/Mathlib community to connect the constructive theorems of Contour 1 to standard `mathlib4` definitions (`RiemannHypothesis`, `RobinInequality`, `Complex`, `Real`).

```bash
# Build Contour 2 (with standard mathlib4):
cd MathlibBridge
lake update
lake build
```

---

## Open Science Invitation & Honest Disclaimer

**Science and mathematics do not belong to isolated individuals — they belong to humanity and to all thinking actors on this planet.**

- All 39 modules in Contour 1 compile with `0 sorryAx` and `0 Classical.choice`.
- However, bridging every constructive theorem to classical continuum definitions in `mathlib4` (Contour 2), cross-checking proofs in independent proof assistants (Coq/Rocq, Isabelle/HOL, Agda) and SMT solvers, and auditing every formulation is too large a task for one person with AI agents.
- Everything is open like Wikipedia. We invite the global Lean, Mathlib, mathematics, and physics communities to inspect, challenge, extend Contour 2 bridges, report issues, and submit Pull Requests.
