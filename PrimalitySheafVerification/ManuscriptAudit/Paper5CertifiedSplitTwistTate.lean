import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.Paper5SplitTwistCertificate
import PrimalitySheafVerification.ManuscriptAudit.Paper5SplitTatePointCounts

/-! A native reference identity and six certified counts give all split twists' Tate coefficients. -/

namespace ManuscriptAudit.Paper5CertifiedSplitTwistTate

open Polynomial Module FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicFrobeniusSexticTwists CubicOrdinatePreservingTwist
open CubicSplitExtensionTraceRecurrence Paper5SplitTwistCertificate PowerTateModule
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

variable {p : ℕ} [Fact p.Prime]
variable (c : Certificate p) (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]

include c in
private theorem two_ne_zero : (2 : L) ≠ 0 := by
  have h : 2 < p := by have := c.lower; omega
  simpa only [map_natCast, Nat.cast_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr
    (small_cast_ne_zero 2 (by decide) h)

include c in
private theorem three_ne_zero : (3 : L) ≠ 0 := by
  have h : 3 < p := by have := c.lower; omega
  simpa only [map_natCast, Nat.cast_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr
    (small_cast_ne_zero 3 (by decide) h)

private theorem primitive_image : IsPrimitiveRoot (algebraMap (ZMod p) L c.z) 3 :=
  c.primitive.map_of_injective (algebraMap (ZMod p) L).injective

/-- The chosen order-three rotation of the actual geometric point group. -/
def referenceRotation : AddMonoid.End (Geometric (ZMod p) L 1) :=
  pointRotation (primitive_image c L).pow_eq_one
    (shortCubic_discriminant_ne_zero (two_ne_zero c L) (three_ne_zero c L)
      ((map_ne_zero (algebraMap (ZMod p) L)).mpr one_ne_zero))

/-- A literal equality of endomorphisms on all geometric points of the reference curve. -/
def IsNativeReference : Prop :=
  arithmeticFrobenius (ZMod p) L 1 =
    c.a • (1 : AddMonoid.End (Geometric (ZMod p) L 1)) + c.b • referenceRotation c L

variable (l : ℕ) [Fact l.Prime]

abbrev action (A : ZMod p) : Module.End ℤ_[l] (Tate l (Geometric (ZMod p) L A)) :=
  endMap l (arithmeticFrobenius (ZMod p) L A)

def basis (hl : l = 2 ∨ l = 3) {A : ZMod p} (hA : A ≠ 0) :
    Basis (Fin 2) ℤ_[l] (Tate l (Geometric (ZMod p) L A)) :=
  CubicRotationTateRankTwo.tateBasis (A := algebraMap (ZMod p) L A)
    (two_ne_zero c L) (three_ne_zero c L) ((map_ne_zero (algebraMap (ZMod p) L)).mpr hA)
    (primitive_image c L).pow_eq_one ((primitive_image c L).ne_one (by decide)) l hl

/-- All nonzero twists have the exact arithmetic Tate trace and determinant. -/
theorem trace_det (hF : IsNativeReference c L) (hl : l = 2 ∨ l = 3) {A : ZMod p} (hA : A ≠ 0) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod p) L A)) (action L l A) =
      (signedTrace A : ℤ_[l]) ∧ LinearMap.det (action L l A) = (p : ℤ_[l]) := by
  have hCard : Fintype.card (ZMod p) = 6 * c.k + 1 := (ZMod.card p).trans c.card
  obtain ⟨ht, hd⟩ := CubicSexticTwistCoefficientFormula.trace_det (A := (1 : ZMod p)) (B := A)
    (two_ne_zero c L) (three_ne_zero c L) one_ne_zero hA hCard c.primitive c.a c.b hF l hl
  rw [c.norm, Int.cast_natCast] at hd
  rw [parameter, div_one] at ht
  change _ = (prediction c A : ℤ_[l]) at ht
  rw [prediction_eq_count c hA] at ht
  exact ⟨ht, hd⟩

/-- Exact characteristic polynomial on the actual Tate module of every nonzero twist. -/
theorem charpoly_eq_count (hF : IsNativeReference c L) (hl : l = 2 ∨ l = 3)
    {A : ZMod p} (hA : A ≠ 0) :
    letI := Module.Free.of_basis (basis c L l hl hA)
    letI := Module.Finite.of_basis (basis c L l hl hA)
    (action L l A).charpoly = X ^ 2 - C (signedTrace A : ℤ_[l]) * X + C (p : ℤ_[l]) := by
  let B := basis c L l hl hA
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det c L l hF hl hA
  change (action L l A).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (action L l A) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

/-- Native Frobenius powers on every twist give the projective point counts over all extensions. -/
theorem trace_eq_extension_count (E : Type*) [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod p) E] (hF : IsNativeReference c L) (hl : l = 2 ∨ l = 3)
    {A : ZMod p} (hA : A ≠ 0) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod p) L A))
      (action L l A ^ Module.finrank (ZMod p) E) =
    (((Fintype.card E : ℤ) + 1 -
      (Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point : ℤ) : ℤ) : ℤ_[l]) := by
  have hmod : p % 3 = 1 := by have := c.card; omega
  obtain ⟨ht, hd⟩ := trace_det c L l hF hl hA
  apply Paper5SplitTatePointCounts.trace_power_eq_extension_count (p := p) (E := E)
    c.lower hmod hA (basis c L l hl hA) (action L l A)
  · simpa only [signedTrace, ZMod.card, paper_curve_eq] using ht
  · exact hd

end
end ManuscriptAudit.Paper5CertifiedSplitTwistTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5CertifiedSplitTwistTate.trace_det,
      ``ManuscriptAudit.Paper5CertifiedSplitTwistTate.charpoly_eq_count,
      ``ManuscriptAudit.Paper5CertifiedSplitTwistTate.trace_eq_extension_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
