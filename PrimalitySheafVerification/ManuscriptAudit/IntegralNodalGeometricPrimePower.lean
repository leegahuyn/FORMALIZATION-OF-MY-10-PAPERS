import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalGeometricEuler
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportCyclicDegrees
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionIsoDomain
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoSmallEtaleCohomology

/-! Prime-power compact groups on the actual geometric pullback of the fixed integral nodal family. -/

namespace ManuscriptAudit.IntegralNodalGeometricPrimePower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralNodalGeometricFiber (closureField geometricFiber projectiveIso)
open IntegralNodalGeometricBoundary (geometricSmoothOpen origin origin_closed geometric_smooth_range
  geometric_preconnected)
open NodalProjectiveClosure (affineNode affineOpen projectiveNode)
open NodalCompactSupportHOne (nodalHc)
open NodalProjectiveCyclicHOne (C)
open OpenEtaleExtension (extensionByZero extensionByZeroIdIso extensionByZeroConstantIsoDomain)
open OpenComplementRationalPointCohomology (extensionH positiveEquiv zero_subsingleton)
open SmallEtaleEquivalenceCohomology (schemeIsoCohomologyEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev A := AddCommGrpCat.{0}
private abbrev M (d : ℕ) := AddCommGrpCat.of (ZMod d)

variable (p : ℕ) [Fact p.Prime]

/-- Pull back the genuine affine nodal chart into the actual geometric fibre. -/
abbrev geometricAffine :=
  pullback (projectiveIso p).hom (affineOpen (closureField p))

def geometricAffineOpen : geometricAffine p ⟶ geometricFiber p :=
  pullback.fst _ _

instance geometricAffineOpen_isOpenImmersion : IsOpenImmersion (geometricAffineOpen p) :=
  inferInstanceAs (IsOpenImmersion (pullback.fst (projectiveIso p).hom (affineOpen (closureField p))))

/-- The affine geometric chart compactified in the proper nodal model. -/
def affineCompactifyingOpen : geometricAffine p ⟶ projectiveNode (closureField p) :=
  geometricAffineOpen p ≫ (projectiveIso p).hom

instance affineCompactifyingOpen_isOpenImmersion : IsOpenImmersion (affineCompactifyingOpen p) := by
  unfold affineCompactifyingOpen
  infer_instance

/-- Compact cohomology of the literal proper geometric fibre. -/
abbrev properHc (d n : ℕ) := extensionH (𝟙 (geometricFiber p)) (M d) n

/-- Compact cohomology of its pulled-back affine nodal chart. -/
abbrev affineHc (d n : ℕ) := extensionH (affineCompactifyingOpen p) (M d) n

/-- Compact cohomology of its actual relative smooth open. -/
abbrev smoothHc (d n : ℕ) := extensionH (geometricSmoothOpen p).ι (M d) n

private def extensionCongr {U X : Scheme.{0}} (j k : U ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) :
    extensionByZero j A ≅ extensionByZero k A := by
  subst k
  exact Iso.refl _

/-- The compact groups of the pulled-back affine chart identify with the native nodal compact groups. -/
def affineModelEquiv (d n : ℕ) :
    affineHc p d n ≃+ nodalHc (closureField p) (M d) n := by
  let K := closureField p
  let j := affineOpen K
  let i : geometricAffine p ⟶ affineNode K := pullback.snd (projectiveIso p).hom j
  letI : IsIso i := inferInstanceAs (IsIso (pullback.snd (projectiveIso p).hom (affineOpen K)))
  let F := (constantSheaf (geometricAffine p).smallEtaleTopology A).obj (M d)
  let h : affineCompactifyingOpen p = i ≫ j := pullback.condition
  let e := (extensionCongr (affineCompactifyingOpen p) (i ≫ j) h).app F
  let f := extensionByZeroConstantIsoDomain i j (M d)
  exact ((Sheaf.functorH (projectiveNode K).smallEtaleTopology n).mapIso
    (e ≪≫ f)).addCommGroupIsoToAddEquiv

/-- Identity extension and the genuine fibre isomorphism identify proper compact cohomology. -/
def properModelEquiv (d n : ℕ) :
    properHc p d n ≃+ Sheaf.H (C (projectiveNode (closureField p)) d) n := by
  let X := geometricFiber p
  let H := Sheaf.functorH X.smallEtaleTopology n
  let e := (H.mapIso ((extensionByZeroIdIso X).app (C X d))).addCommGroupIsoToAddEquiv
  exact e.trans (schemeIsoCohomologyEquiv (projectiveIso p) (M d) n)

/-- The positive compact groups of the actual smooth open compare through the rational origin. -/
def smoothPositiveModelEquiv (d n : ℕ) :
    smoothHc p d (n + 1) ≃+ Sheaf.H (C (projectiveNode (closureField p)) d) (n + 1) := by
  letI := origin_closed p
  exact (positiveEquiv (geometricSmoothOpen p).ι (closureField p) (origin p) (geometric_smooth_range p)
    (M d) n).trans (schemeIsoCohomologyEquiv (projectiveIso p) (M d) (n + 1))

theorem smoothHZero_subsingleton (d : ℕ) : Subsingleton (smoothHc p d 0) := by
  letI := origin_closed p
  letI := geometric_preconnected p
  exact zero_subsingleton (geometricSmoothOpen p).ι (closureField p) (origin p) (geometric_smooth_range p) (M d)

private theorem two_ne_zero (hp : 2 < p) : (2 : closureField p) ≠ 0 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IntegralNodalGeometricEuler.coefficient_ne_zero p 2 (ne_of_lt hp)

variable (ℓ : ℕ) [Fact ℓ.Prime]

private theorem power_ne_zero (hℓp : ℓ ≠ p) (r : ℕ) : ((ℓ ^ r : ℕ) : closureField p) ≠ 0 := by
  rw [Nat.cast_pow]
  exact pow_ne_zero r (IntegralNodalGeometricEuler.coefficient_ne_zero p ℓ hℓp)

/-- Compact cohomology of the actual proper geometric fibre for every ℓ-power order. -/
def properEquiv (hp : 2 < p) (hℓp : ℓ ≠ p) (r n : ℕ) :
    properHc p (ℓ ^ r) n ≃+ ZMod (if n ≤ 2 then ℓ ^ r else 1) := by
  letI : NeZero ((ℓ ^ r : ℕ) : closureField p) := ⟨power_ne_zero p ℓ hℓp r⟩
  exact (properModelEquiv p (ℓ ^ r) n).trans
    (NodalCompactSupportCyclicDegrees.ordinaryEquiv (closureField p) (ℓ ^ r) (two_ne_zero p hp) n)

/-- Compact cohomology of the actual affine chart for every ℓ-power order. -/
def affineEquiv (hp : 2 < p) (hℓp : ℓ ≠ p) (r n : ℕ) :
    affineHc p (ℓ ^ r) n ≃+ ZMod (if n = 1 ∨ n = 2 then ℓ ^ r else 1) := by
  letI : NeZero ((ℓ ^ r : ℕ) : closureField p) := ⟨power_ne_zero p ℓ hℓp r⟩
  exact (affineModelEquiv p (ℓ ^ r) n).trans
    (NodalCompactSupportCyclicDegrees.affineEquiv (closureField p) (ℓ ^ r) (two_ne_zero p hp) n)

/-- Compact cohomology of the actual relative smooth open for every ℓ-power order. -/
def smoothEquiv (hp : 2 < p) (hℓp : ℓ ≠ p) (r n : ℕ) :
    smoothHc p (ℓ ^ r) n ≃+ ZMod (if n = 1 ∨ n = 2 then ℓ ^ r else 1) := by
  letI : NeZero ((ℓ ^ r : ℕ) : closureField p) := ⟨power_ne_zero p ℓ hℓp r⟩
  cases n with
  | zero =>
    change smoothHc p (ℓ ^ r) 0 ≃+ ZMod 1
    let h := smoothHZero_subsingleton p (ℓ ^ r)
    exact AddEquiv.ofBijective (0 : smoothHc p (ℓ ^ r) 0 →+ ZMod 1)
      ⟨fun _ _ _ ↦ h.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  | succ n =>
    have hOrder : (if n + 1 ≤ 2 then ℓ ^ r else 1) =
        (if n + 1 = 1 ∨ n + 1 = 2 then ℓ ^ r else 1) := by
      have h : n + 1 ≤ 2 ↔ n + 1 = 1 ∨ n + 1 = 2 := by omega
      rw [h]
    let e := NodalCompactSupportCyclicDegrees.ordinaryEquiv (closureField p) (ℓ ^ r)
      (two_ne_zero p hp) (n + 1)
    exact (smoothPositiveModelEquiv p (ℓ ^ r) n).trans (e.trans (ZMod.ringEquivCongr hOrder).toAddEquiv)

end
end ManuscriptAudit.IntegralNodalGeometricPrimePower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalGeometricPrimePower.affineModelEquiv,
      ``ManuscriptAudit.IntegralNodalGeometricPrimePower.properModelEquiv,
      ``ManuscriptAudit.IntegralNodalGeometricPrimePower.smoothPositiveModelEquiv,
      ``ManuscriptAudit.IntegralNodalGeometricPrimePower.smoothHZero_subsingleton,
      ``ManuscriptAudit.IntegralNodalGeometricPrimePower.properEquiv,
      ``ManuscriptAudit.IntegralNodalGeometricPrimePower.affineEquiv,
      ``ManuscriptAudit.IntegralNodalGeometricPrimePower.smoothEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
