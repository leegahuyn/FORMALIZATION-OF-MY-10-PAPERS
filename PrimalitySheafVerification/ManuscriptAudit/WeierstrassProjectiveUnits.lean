import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffineUnits
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveClosure

/-! Global units on the actual proper Weierstrass closure are exactly scalars. -/

namespace ManuscriptAudit.WeierstrassProjectiveUnits

open AlgebraicGeometry CategoryTheory WeierstrassProjectiveClosure
open CuspProperCompactification (projectivePlane)

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

private abbrev A := CommRingCat.of W.CoordinateRing
private abbrev B := Γ(projectiveScheme W, ⊤)

/-- The genuine restriction of global projective sections to affine coordinates. -/
def restriction : B W ⟶ A W :=
  (WeierstrassProjectiveClosure.affineOpen W).appTop ≫ (Scheme.ΓSpecIso (A W)).hom

private theorem restriction_injective : Function.Injective (restriction W).hom := by
  letI : QuasiCompact (inPlane W) := quasiCompact_of_compactSpace _
  have hj : Function.Injective (WeierstrassProjectiveClosure.affineOpen W).appTop := by
    let j := WeierstrassProjectiveClosure.affineOpen W
    change Function.Injective (j.app ⊤)
    rw [injective_iff_map_eq_zero]
    intro s hs
    refine (projectiveScheme W).IsSheaf.section_ext fun x _ => ?_
    let y := (inPlane W).imageι x
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      (projectivePlane K).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    let U : (projectiveScheme W).Opens := (inPlane W).imageι ⁻¹ᵁ V
    let i : U ⟶ (⊤ : (projectiveScheme W).Opens) := homOfLE le_top
    refine ⟨U, le_top, hyV, (inPlane W).toImage_app_injective ⟨V, hV⟩ ?_⟩
    change j.app U ((projectiveScheme W).presheaf.map i.op s) =
      j.app U ((projectiveScheme W).presheaf.map i.op 0)
    simp only [map_zero]
    rw [← ConcreteCategory.comp_apply, j.naturality]
    change (j.app ⊤).hom s = 0 at hs
    change ((affineScheme W).presheaf.map
      ((TopologicalSpace.Opens.map j.base).map i).op).hom ((j.app ⊤).hom s) = 0
    rw [hs, map_zero]
  exact (Scheme.ΓSpecIso (A W)).commRingCatIsoToRingEquiv.injective.comp hj

/-- Constants in the actual global functions of the projective scheme. -/
def scalarMap : CommRingCat.of K ⟶ B W :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (toBase W).appTop

theorem scalarMap_restriction :
    scalarMap W ≫ restriction W = CommRingCat.ofHom (algebraMap K W.CoordinateRing) := by
  let F := CommRingCat.ofHom (algebraMap K W.CoordinateRing)
  have h : (toBase W).appTop ≫ (WeierstrassProjectiveClosure.affineOpen W).appTop = (Spec.map F).appTop := by
    rw [← Scheme.Hom.comp_appTop, affineOpen_toBase]
  calc
    scalarMap W ≫ restriction W = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        ((toBase W).appTop ≫ (WeierstrassProjectiveClosure.affineOpen W).appTop) ≫
        (Scheme.ΓSpecIso (A W)).hom := by simp [scalarMap, restriction, Category.assoc]
    _ = CommRingCat.ofHom (algebraMap K W.CoordinateRing) := by
      rw [h, Scheme.ΓSpecIso_naturality]
      simp [F]

private theorem scalar_restrict_value (a : K) :
    (restriction W).hom ((scalarMap W).hom a) = algebraMap K W.CoordinateRing a :=
  congrArg (fun f : CommRingCat.of K ⟶ A W => f.hom a) (scalarMap_restriction W)

/-- The multiplicative group of actual global units on the projective closure. -/
def unitsEquiv : Kˣ ≃* (B W)ˣ := by
  refine MulEquiv.ofBijective (Units.map (scalarMap W).hom) ⟨?_, ?_⟩
  · intro a b h
    apply Units.ext
    apply (algebraMap K W.CoordinateRing).injective
    have hh := congrArg (fun x : (B W)ˣ => (restriction W).hom (x : B W)) h
    exact (scalar_restrict_value W a).symm.trans (hh.trans (scalar_restrict_value W b))
  · intro u
    obtain ⟨a, ha⟩ := (WeierstrassAffineUnits.unitsEquiv W).surjective
      (Units.map (restriction W).hom u)
    have hu := congrArg (fun x : W.CoordinateRingˣ => (x : W.CoordinateRing)) ha
    apply Exists.intro a
    apply Units.ext
    apply restriction_injective W
    change (restriction W).hom ((scalarMap W).hom (a : K)) = (restriction W).hom (u : B W)
    exact (scalar_restrict_value W a).trans
      ((WeierstrassAffineUnits.unitsEquiv_apply_val W a).symm.trans hu)

theorem unit_power_surjective [IsAlgClosed K] (d : ℕ) (hd : 0 < d) :
    Function.Surjective (fun u : (B W)ˣ => u ^ d) := by
  intro u
  obtain ⟨a, rfl⟩ := (unitsEquiv W).surjective u
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : K) hd
  have hbn : b ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne'] at hb
    exact a.ne_zero hb.symm
  refine ⟨unitsEquiv W (Units.mk0 b hbn), ?_⟩
  change (unitsEquiv W (Units.mk0 b hbn)) ^ d = unitsEquiv W a
  rw [← map_pow]
  apply congrArg (unitsEquiv W)
  exact Units.ext hb

end

end ManuscriptAudit.WeierstrassProjectiveUnits

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveUnits.scalarMap_restriction,
      ``ManuscriptAudit.WeierstrassProjectiveUnits.unitsEquiv,
      ``ManuscriptAudit.WeierstrassProjectiveUnits.unit_power_surjective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
