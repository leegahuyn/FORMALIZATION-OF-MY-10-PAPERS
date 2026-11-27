import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeFrobeniusMatrix

/-! Native q-Frobenius on the centered cubic over an arbitrary finite field. -/

namespace ManuscriptAudit.CubicThreeFrobeniusActual

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion
open CubicThreeTorsionOrdinate CubicThreeTorsionBasis CubicThreeFrobeniusSigns
open CubicThreeFrobeniusMatrix TorsionFrobeniusModule

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable (E : Type*) [Field E]
variable (L : Type*) [Field L] [Algebra E L] [DecidableEq L]

abbrev ActualTorsion (A : E) := Torsion 3 ((Curve A).baseChange L).Point

private def curveTransport {W V : Affine L} (h : W = V) :
    Torsion 3 W.Point ≃ₗ[ZMod 3] Torsion 3 V.Point := by
  subst V
  exact LinearEquiv.refl _ _

private def rawAbscissa {W : Affine L} : W.Point → L
  | .zero => 0
  | .some x _ _ => x

private def rawOrdinate {W : Affine L} : W.Point → L
  | .zero => 0
  | .some _ y _ => y

private theorem conjugate_pointMap_abscissa (W : Affine E) (V : Affine L)
    (hW : W.baseChange L = V) (g : L →ₐ[E] L) (P : Torsion 3 V.Point) :
    rawAbscissa L (inclusion 3 _ ((curveTransport L hW).conj (pointMap 3 W g) P)) =
      g (rawAbscissa L (inclusion 3 _ P)) := by
  subst V
  change rawAbscissa L (Affine.Point.map (W' := W) g (inclusion 3 _ P)) = _
  generalize inclusion 3 _ P = Q
  cases Q with
  | zero =>
    change (0 : L) = g 0
    exact (map_zero g).symm
  | some x y h => rfl

private theorem conjugate_pointMap_ordinate (W : Affine E) (V : Affine L)
    (hW : W.baseChange L = V) (g : L →ₐ[E] L) (P : Torsion 3 V.Point) :
    rawOrdinate L (inclusion 3 _ ((curveTransport L hW).conj (pointMap 3 W g) P)) =
      g (rawOrdinate L (inclusion 3 _ P)) := by
  subst V
  change rawOrdinate L (Affine.Point.map (W' := W) g (inclusion 3 _ P)) = _
  generalize inclusion 3 _ P = Q
  cases Q with
  | zero =>
    change (0 : L) = g 0
    exact (map_zero g).symm
  | some x y h => rfl

private theorem rawAbscissa_centered {A : L} (P : (Curve A).Point) :
    rawAbscissa L P = abscissa P := by cases P <;> rfl

private theorem rawOrdinate_centered {A : L} (P : (Curve A).Point) :
    rawOrdinate L P = ordinate P := by cases P <;> rfl

private theorem centered_baseChange (A : E) :
    (Curve A).baseChange L = Curve (algebraMap E L A) := by
  simp [Curve, CubicAffine, shortCubic, WeierstrassCurve.baseChange, WeierstrassCurve.map]

private def centeredTransport (A : E) :
    ActualTorsion E L A ≃ₗ[ZMod 3] T₃ (algebraMap E L A) :=
  curveTransport L (centered_baseChange E L A)

private theorem mapped_nonzero (a : E) (ha : a ≠ 0) : algebraMap E L a ≠ 0 :=
  (map_ne_zero (algebraMap E L)).mpr ha

variable [Fintype E] [IsAlgClosed L]

/-- The native point-group map of the actual q-power endomorphism, restricted to three-torsion. -/
def actualFrobenius (A : E) : Module.End (ZMod 3) (ActualTorsion E L A) :=
  pointMap 3 (Curve A) (FiniteField.frobeniusAlgHom E L)

/-- A two-element basis of the actual geometric three-torsion. -/
def actualTorsionBasis {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) : Module.Basis (Fin 2) (ZMod 3) (ActualTorsion E L A) := by
  have h₂L : (2 : L) ≠ 0 := by simpa only [map_ofNat] using mapped_nonzero E L 2 h₂
  have h₃L : (3 : L) ≠ 0 := by simpa only [map_ofNat] using mapped_nonzero E L 3 h₃
  have hAL := mapped_nonzero E L A hA
  let D := Classical.choice (flexPair_nonempty h₂L hAL)
  exact (basis h₂L h₃L hAL D).map (centeredTransport E L A).symm

theorem finiteActualTorsionModule {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) : Module.Finite (ZMod 3) (ActualTorsion E L A) :=
  Module.Finite.of_basis (actualTorsionBasis E L h₂ h₃ hA)

/-- The actual q-power point map has the determinant and trace given by the vertical Frobenius sign. -/
theorem actualFrobenius_trace_det {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hA : A ≠ 0) (hq : Fintype.card E % 3 ≠ 0) :
    ∃ a : L, ∃ s : Bool,
      a ^ 2 = algebraMap E L A ∧ a ^ Fintype.card E = signed s a ∧
      LinearMap.det (actualFrobenius E L A) = (Fintype.card E : ZMod 3) ∧
      LinearMap.trace (ZMod 3) (ActualTorsion E L A) (actualFrobenius E L A) =
        if Fintype.card E % 3 = 1 then -signScalar s else 0 := by
  let f := actualFrobenius E L A
  let e := centeredTransport E L A
  let g := FiniteField.frobeniusAlgHom E L
  have h₂L : (2 : L) ≠ 0 := by simpa only [map_ofNat] using mapped_nonzero E L 2 h₂
  have h₃L : (3 : L) ≠ 0 := by simpa only [map_ofNat] using mapped_nonzero E L 3 h₃
  have hAL := mapped_nonzero E L A hA
  let D := Classical.choice (flexPair_nonempty h₂L hAL)
  have hg (x : L) : g x = x ^ Fintype.card E := rfl
  have hfix : g (algebraMap E L A) = algebraMap E L A := g.commutes A
  have hx (P : T₃ (algebraMap E L A)) :
      abscissa (inclusion 3 _ (e.conj f P)) = g (abscissa (inclusion 3 _ P)) := by
    simpa only [rawAbscissa_centered, e, f, centeredTransport, actualFrobenius] using
      conjugate_pointMap_abscissa E L (Curve A) _ (centered_baseChange E L A) g P
  have hy (P : T₃ (algebraMap E L A)) :
      ordinate (inclusion 3 _ (e.conj f P)) = g (ordinate (inclusion 3 _ P)) := by
    simpa only [rawOrdinate_centered, e, f, centeredTransport, actualFrobenius] using
      conjugate_pointMap_ordinate E L (Curve A) _ (centered_baseChange E L A) g P
  obtain ⟨s, hs, hDet, hTrace⟩ :=
    trace_det_of_coordinates h₂L h₃L hAL D (g : L →+* L) (e.conj f)
      (Fintype.card E) hq hg hfix hx hy
  have hd : LinearMap.det (e.conj f) = LinearMap.det f := LinearMap.det_conj f e
  have ht : LinearMap.trace (ZMod 3) _ (e.conj f) = LinearMap.trace (ZMod 3) _ f :=
    LinearMap.trace_conj' f e
  exact ⟨D.a, s, D.a_square, (hg D.a).symm.trans hs, hd.symm.trans hDet, ht.symm.trans hTrace⟩

end
end ManuscriptAudit.CubicThreeFrobeniusActual

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicThreeFrobeniusActual.actualTorsionBasis,
      ``ManuscriptAudit.CubicThreeFrobeniusActual.actualFrobenius_trace_det] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
