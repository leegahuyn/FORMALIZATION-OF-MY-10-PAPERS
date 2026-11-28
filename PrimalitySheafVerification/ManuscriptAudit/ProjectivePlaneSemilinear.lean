import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import PrimalitySheafVerification.ManuscriptAudit.CuspYChartAlgebra

/-! The literal homogeneous coefficient map of projective coordinates
induces the actual semilinear map of projective planes. -/

namespace ManuscriptAudit.ProjectivePlaneSemilinear

open AlgebraicGeometry CategoryTheory
open CuspYChartAlgebra HomogeneousIdeal

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {K L : Type u} [Field K] [Field L]

/-- The native graded map applies the coefficient homomorphism and leaves all homogeneous variables fixed. -/
def coefficientMap (e : K →+* L) : grading K →+*ᵍ grading L :=
  ⟨MvPolynomial.map e, fun {n x} hx => (show x.IsHomogeneous n from hx).map e⟩

theorem coefficientMap_var (e : K →+* L) (i : Fin 3) :
    coefficientMap e (MvPolynomial.X i) = MvPolynomial.X i :=
  MvPolynomial.map_X _ _

theorem coefficientMap_const (e : K →+* L) (x : K) :
    coefficientMap e (MvPolynomial.C x) = MvPolynomial.C (e x) :=
  MvPolynomial.map_C _ _

private theorem coefficientMap_comp_inv (e : K ≃+* L) :
    (coefficientMap e.toRingHom).comp (coefficientMap e.symm.toRingHom) = GradedRingHom.id (grading L) := by
  apply GradedRingHom.ext
  intro x
  change MvPolynomial.map e.toRingHom (MvPolynomial.map e.symm.toRingHom x) = x
  rw [MvPolynomial.map_map]
  have h : e.toRingHom.comp e.symm.toRingHom = RingHom.id L := RingHom.ext e.apply_symm_apply
  rw [h, MvPolynomial.map_id]

private theorem irrelevant_le_map (e : K ≃+* L) :
    HomogeneousIdeal.irrelevant (grading L) ≤
      (HomogeneousIdeal.irrelevant (grading K)).map (coefficientMap e.toRingHom) := by
  apply (HomogeneousIdeal.irrelevant_le (grading L)).mpr
  intro n hn x hx
  let y := coefficientMap e.symm.toRingHom x
  have hy : y ∈ grading K n := (coefficientMap e.symm.toRingHom).map_mem hx
  have hxy : coefficientMap e.toRingHom y = x :=
    DFunLike.congr_fun (coefficientMap_comp_inv e) x
  change x ∈ Ideal.map (coefficientMap e.toRingHom).toRingHom (HomogeneousIdeal.irrelevant (grading K)).toIdeal
  rw [← hxy]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem (grading K) hn hy)

private theorem map_congr {f g : grading K →+*ᵍ grading L}
    (hf : HomogeneousIdeal.irrelevant (grading L) ≤
      (HomogeneousIdeal.irrelevant (grading K)).map f)
    (hg : HomogeneousIdeal.irrelevant (grading L) ≤
      (HomogeneousIdeal.irrelevant (grading K)).map g)
    (h : f = g) : Proj.map f hf = Proj.map g hg := by
  subst g
  rfl

/-- The genuine projective-plane scheme isomorphism induced by a field isomorphism. -/
def planeIso (e : K ≃+* L) : plane L ≅ plane K where
  hom := Proj.map (coefficientMap e.toRingHom) (irrelevant_le_map e)
  inv := Proj.map (coefficientMap e.symm.toRingHom) (irrelevant_le_map e.symm)
  hom_inv_id := by
    rw [← Proj.map_comp]
    exact (map_congr _ _ (coefficientMap_comp_inv e)).trans Proj.map_id
  inv_hom_id := by
    rw [← Proj.map_comp]
    have h := coefficientMap_comp_inv e.symm
    change (coefficientMap e.symm.toRingHom).comp (coefficientMap e.toRingHom) = _ at h
    exact (map_congr _ _ h).trans Proj.map_id

end

end ManuscriptAudit.ProjectivePlaneSemilinear

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProjectivePlaneSemilinear.planeIso
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
