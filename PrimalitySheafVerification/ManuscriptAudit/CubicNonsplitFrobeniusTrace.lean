import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationConjugacyTrace
import PrimalitySheafVerification.ManuscriptAudit.CubicThreePointCounts

/-! Actual Frobenius trace zero on all two-power levels of the centered nonsplit family. -/

namespace ManuscriptAudit.CubicNonsplitFrobeniusTrace

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion
open CubicThreeTorsionOrdinate CubicThreeTorsionCard CubicCubeRotation
open CubicRotationConjugacyTrace CubicThreeFrobeniusSigns CubicThreePointCounts
open TorsionFrobeniusModule TwoPowerTorsionTower

noncomputable section

theorem exists_nontrivial_cubeRoot {K : Type*} [Field K] [IsAlgClosed K] (h₃ : (3 : K) ≠ 0) :
    ∃ z : K, z ^ 3 = 1 ∧ z ≠ 1 := by
  let f : K[X] := X ^ 2 + (X + C 1)
  have hlt : ((X : K[X]) + C 1).natDegree < ((X : K[X]) ^ 2).natDegree := by
    rw [natDegree_add_C, natDegree_X, natDegree_X_pow]
    decide
  have hd : f.natDegree = 2 := by
    dsimp only [f]
    rw [natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_X_pow]
  have hf : f ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hd
    contradiction
  have hdegree : f.degree ≠ 0 := by
    rw [degree_eq_natDegree hf, hd]
    decide
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root f hdegree
  have hcy : z ^ 2 + z + 1 = 0 := by
    have he : f.eval z = 0 := hz
    simpa [f, add_assoc] using he
  have hz₃ : z ^ 3 = 1 := sub_eq_zero.mp (by
    calc
      _ = (z - 1) * (z ^ 2 + z + 1) := by ring
      _ = _ := by rw [hcy, mul_zero])
  refine ⟨z, hz₃, ?_⟩
  intro he
  rw [he] at hcy
  apply h₃
  calc
    (3 : K) = 1 ^ 2 + 1 + 1 := by ring
    _ = 0 := hcy

variable (E : Type*) [Field E]
variable (L : Type*) [Field L] [Algebra E L] [DecidableEq L]

private def pointTransport {W V : Affine L} (h : W = V) : W.Point ≃+ V.Point := by
  subst V
  exact AddEquiv.refl _

private def torsionTransport (m : ℕ) {W V : Affine L} (h : W = V) :
    Torsion m W.Point ≃ₗ[ZMod m] Torsion m V.Point := by
  subst V
  exact LinearEquiv.refl _ _

private def pointMapAt (W : Affine E) (V : Affine L) (hW : W.baseChange L = V)
    (g : L →ₐ[E] L) : V.Point →+ V.Point :=
  let e := pointTransport L hW
  e.toAddMonoidHom.comp ((Affine.Point.map (W' := W) g).comp e.symm.toAddMonoidHom)

private theorem pointMapAt_some (W : Affine E) (V : Affine L) (hW : W.baseChange L = V)
    (g : L →ₐ[E] L) (x y : L) (h : V.Nonsingular x y) :
    ∃ h' : V.Nonsingular (g x) (g y),
      pointMapAt E L W V hW g (Affine.Point.some x y h) =
        Affine.Point.some (g x) (g y) h' := by
  subst V
  refine ⟨(W.baseChange_nonsingular (f := g) g.injective x y).mpr h, ?_⟩
  rfl

private theorem mapLinear_transport (W : Affine E) (V : Affine L) (hW : W.baseChange L = V)
    (g : L →ₐ[E] L) (m : ℕ) :
    (torsionTransport L m hW).conj (pointMap m W g) =
      mapLinear m (pointMapAt E L W V hW g) := by
  subst V
  ext P
  rfl

private theorem pointMapAt_conjugates_rotation (W : Affine E) {a z : L}
    (hW : W.baseChange L = Curve a) (g : L →ₐ[E] L) (hgz : g z = z ^ 2)
    (hz : z ^ 3 = 1) (hΔ : (shortCubic (0 : L) a).Δ ≠ 0)
    (P : (Curve a).Point) :
    let f := pointMapAt E L W (Curve a) hW g
    let r := rotate z hz hΔ
    f (r P) = r (r (f P)) := by
  let f := pointMapAt E L W (Curve a) hW g
  let r := rotate z hz hΔ
  change f (r P) = r (r (f P))
  cases P with
  | zero =>
    change f (r 0) = r (r (f 0))
    simp only [map_zero]
  | some x y h =>
    have hr : (Curve a).Nonsingular (z * x) y := by
      apply (nonsingular_iff hΔ _ _).mpr
      rw [mul_pow, hz, one_mul]
      exact (nonsingular_iff hΔ _ _).mp h
    have hP : r (Affine.Point.some x y h) = Affine.Point.some (z * x) y hr :=
      rotate_some hz hΔ h
    obtain ⟨h₁, he₁⟩ := pointMapAt_some E L W (Curve a) hW g (z * x) y hr
    obtain ⟨h₂, he₂⟩ := pointMapAt_some E L W (Curve a) hW g x y h
    change f (Affine.Point.some (z * x) y hr) = _ at he₁
    change f (Affine.Point.some x y h) = _ at he₂
    rw [hP, he₁, he₂]
    change Affine.Point.some (g (z * x)) (g y) h₁ =
      rotate z hz hΔ (rotate z hz hΔ (Affine.Point.some (g x) (g y) h₂))
    rw [rotate_some, rotate_some, Affine.Point.some.injEq]
    exact ⟨by rw [map_mul, hgz, pow_two, mul_assoc], rfl⟩

private theorem centered_baseChange (A : E) :
    (Curve A).baseChange L = Curve (algebraMap E L A) := by
  simp [Curve, CubicAffine, shortCubic, WeierstrassCurve.baseChange, WeierstrassCurve.map]

variable [Fintype E] [IsAlgClosed L]

/-- The actual restricted q-power map, with level scalar ring ZMod(2^n). -/
def actualFrobenius (A : E) (n : ℕ) :
    Module.End (ZMod (2 ^ n)) (PowerTorsion ((Curve A).baseChange L).Point n) :=
  pointMap (2 ^ n) (Curve A) (FiniteField.frobeniusAlgHom E L)

/-- The arithmetic q-power Frobenius has exact trace zero at every native 2-power level. -/
theorem actual_trace_zero {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq : Fintype.card E % 3 = 2) (n : ℕ) :
    LinearMap.trace (ZMod (2 ^ n)) (PowerTorsion ((Curve A).baseChange L).Point n)
      (actualFrobenius E L A n) = 0 := by
  cases n with
  | zero =>
    letI : Subsingleton (ZMod (2 ^ 0)) := inferInstanceAs (Subsingleton (ZMod 1))
    exact Subsingleton.elim _ _
  | succ n =>
    let a := algebraMap E L A
    have h₂L : (2 : L) ≠ 0 := by
      have h := (map_ne_zero (algebraMap E L)).mpr h₂
      simpa only [map_ofNat] using h
    have h₃L : (3 : L) ≠ 0 := by
      have h := (map_ne_zero (algebraMap E L)).mpr h₃
      simpa only [map_ofNat] using h
    have ha : a ≠ 0 := (map_ne_zero (algebraMap E L)).mpr hA
    let hΔ := shortCubic_discriminant_ne_zero h₂L h₃L ha
    let he := centered_baseChange E L A
    let g := FiniteField.frobeniusAlgHom E L
    obtain ⟨z, hz, hz₁⟩ := exists_nontrivial_cubeRoot h₃L
    have hg : g z = z ^ 2 := by
      change z ^ Fintype.card E = z ^ 2
      rw [pow_cube_reduce z _ hz, hq]
    let f := pointMapAt E L (Curve A) (Curve a) he g
    have hf (P : (Curve a).Point) : f (rotate z hz hΔ P) = rotate z hz hΔ (rotate z hz hΔ (f P)) :=
      pointMapAt_conjugates_rotation E L (Curve A) he g hg hz hΔ P
    let e := torsionTransport L (2 ^ (n + 1)) he
    have hTrace := (trace_det_of_point_conjugacy h₂L h₃L ha hz hz₁ f hf n).1
    rw [← LinearMap.trace_conj' _ e]
    change LinearMap.trace (ZMod (2 ^ (n + 1))) _ (e.conj (pointMap (2 ^ (n + 1)) (Curve A) g)) = 0
    rw [mapLinear_transport E L (Curve A) (Curve a) he g]
    exact hTrace

/-- The trace agrees with the signed actual arithmetic point count modulo every power of two. -/
theorem actual_trace_eq_signed_point_count {A : E} [DecidableEq E]
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq : Fintype.card E % 3 = 2) (n : ℕ) :
    LinearMap.trace (ZMod (2 ^ n)) (PowerTorsion ((Curve A).baseChange L).Point n)
      (actualFrobenius E L A n) =
      (((Fintype.card E : ℤ) + 1 -
        (Nat.card (shortCubic (0 : E) A).toProjective.Point : ℤ)) : ZMod (2 ^ n)) := by
  rw [actual_trace_zero E L h₂ h₃ hA hq n, projective_count_residue_two A h₂ h₃ hA hq]
  simp [Nat.cast_add]

end
end ManuscriptAudit.CubicNonsplitFrobeniusTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicNonsplitFrobeniusTrace.exists_nontrivial_cubeRoot,
      ``ManuscriptAudit.CubicNonsplitFrobeniusTrace.actual_trace_zero,
      ``ManuscriptAudit.CubicNonsplitFrobeniusTrace.actual_trace_eq_signed_point_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
