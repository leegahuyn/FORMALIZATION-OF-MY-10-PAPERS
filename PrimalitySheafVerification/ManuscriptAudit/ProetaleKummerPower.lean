import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.EpiMono
import PrimalitySheafVerification.ManuscriptAudit.KummerSiteCover
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenCover
import PrimalitySheafVerification.ManuscriptAudit.ProetaleUnitSheaf

/-! The genuine power map of the native pro-étale units sheaf is an
epimorphism when its degree is invertible over the coefficient field. -/

namespace ManuscriptAudit.ProetaleKummerPower

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleUnitSheaf KummerSiteCover

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}}

abbrev J (X : Scheme.{0}) := Scheme.ProEt.topology X
abbrev G := AddCommGrpCat.{1}

/-- The actual multiplication-by-d endomorphism of the additive units sheaf. -/
def power (X : Scheme.{0}) (d : ℕ) : unitSheaf X ⟶ unitSheaf X := d • 𝟙 _

theorem power_eval (d : ℕ) {U : X.ProEt} (s : (unitSheaf X).obj.obj (op U)) :
    (power X d).hom.app (op U) s = d • s := by
  let P := sheafToPresheaf (J X) G ⋙ (evaluation X.ProEtᵒᵖ G).obj (op U)
  let Q := P.obj (unitSheaf X)
  change (P.map (d • 𝟙 (unitSheaf X)) : Q ⟶ Q) s = d • s
  rw [Functor.map_nsmul, P.map_id]
  rfl

variable {R : CommRingCat.{0}} (g : Spec R ⟶ X) [WeaklyEtale g]
  (d : ℕ) (hpos : 0 < d) (hd : IsUnit (d : R))

include hpos hd in
/-- A unit on a displayed affine weakly étale chart has a d-th root
on a native covering arrow, given by the finite étale root algebra. -/
theorem imageSieve_mem_of_spec (s : (unitSheaf X).obj.obj (op (Scheme.ProEt.mk g))) :
    Presheaf.imageSieve (power X d).hom s ∈ J X (Scheme.ProEt.mk g) := by
  let a := (specUnits R g s).toMul
  let B := rootAlgebra d a
  let e := rootMap d a
  have h := KummerEtale.kummer_spec_finite_etale_cover hpos hd a.isUnit
  letI : Etale e := h.2.1
  letI : Surjective e := h.2.2
  let U := Scheme.ProEt.mk g
  let V := Scheme.ProEt.mk (e ≫ g)
  let f : V ⟶ U := MorphismProperty.Over.homMk e rfl
  have hCov : Sieve.generate (Presieve.singleton f) ∈ J X U := by
    apply Precoverage.generate_mem_toGrothendieck
    change (Presieve.singleton f).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
      Scheme.proetalePrecoverage U.left
    rw [Presieve.map_singleton]
    change Presieve.singleton e ∈ Scheme.propQCPrecoverage @WeaklyEtale (Spec R)
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (inferInstanceAs (WeaklyEtale e))
  apply (J X).superset_covering _ hCov
  rw [Sieve.generate_le_iff]
  intro W j hj
  cases hj
  obtain ⟨v, hv⟩ := KummerEtale.kummer_root_isUnit hpos a.isUnit
  let t := (specUnits (CommRingCat.of B) (e ≫ g)).symm (Additive.ofMul v)
  refine ⟨t, (specUnits (CommRingCat.of B) (e ≫ g)).injective ?_⟩
  rw [power_eval, map_nsmul, AddEquiv.apply_symm_apply]
  have hu := specUnits_naturality (CommRingCat.ofHom (algebraMap R B)) g s
  change d • Additive.ofMul v = specUnits (CommRingCat.of B) (e ≫ g) ((unitSheaf X).obj.map f.op s)
  rw [hu]
  apply Additive.ext
  apply Units.ext
  change (v : B) ^ d = algebraMap R B (a : R)
  rw [hv]
  exact KummerEtale.kummer_root_pow d (a : R)

variable {K : Type} [Field K] (k : X ⟶ Spec (CommRingCat.of K))

include k in
/-- The native Kummer power map is locally surjective on all
pro-étale objects, by ordinary affine open covers. -/
theorem power_locallySurjective (d : ℕ) (hpos : 0 < d) [NeZero (d : K)] :
    Presheaf.IsLocallySurjective (J X) (power X d).hom where
  imageSieve_mem {U} s := by
    let C := U.left.affineOpenCover
    let O := C.openCover
    apply ProetaleOpenCover.covering_of_covering_on_open U O
    intro i
    rw [Presheaf.pullback_imageSieve]
    let R := C.X i
    let g : Spec R ⟶ X := C.f i ≫ U.hom
    letI : WeaklyEtale g := inferInstance
    let r : CommRingCat.of K ⟶ R := Spec.preimage (g ≫ k)
    have hd : IsUnit (d : R) := by
      simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr (NeZero.ne (d : K))).map r.hom
    exact imageSieve_mem_of_spec g d hpos hd _

include k in
/-- The native power map is an epimorphism. -/
theorem power_epi (d : ℕ) (hpos : 0 < d) [NeZero (d : K)] : Epi (power X d) :=
  (Sheaf.isLocallySurjective_iff_epi' G (power X d)).mp (power_locallySurjective k d hpos)

end
end ManuscriptAudit.ProetaleKummerPower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleKummerPower.imageSieve_mem_of_spec,
      ``ManuscriptAudit.ProetaleKummerPower.power_locallySurjective,
      ``ManuscriptAudit.ProetaleKummerPower.power_epi] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
