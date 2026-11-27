import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import PrimalitySheafVerification.ManuscriptAudit.GaloisCoverAction
import PrimalitySheafVerification.ManuscriptAudit.GaloisOverlapLift
import PrimalitySheafVerification.ManuscriptAudit.GaloisOverlapSections
import PrimalitySheafVerification.ManuscriptAudit.InjectiveCechOne

/-! An injective étale sheaf has no degree-one Galois cohomology on a finite cover. -/

namespace ManuscriptAudit.GaloisCoverAction

open CategoryTheory AlgebraicGeometry Opposite groupCohomology
open GaloisTensorSquare

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [Module.Finite K L] [IsGalois K L]

private abbrev X := Spec (CommRingCat.of K)
private abbrev J := (X K).smallEtaleTopology

variable (M : Sheaf (J K) AddCommGrpCat.{0})

private theorem restrict_comp {U V W : (X K).Etale}
    (f : U ⟶ V) (g : V ⟶ W) (z : M.obj.obj (op W)) :
    M.obj.map f.op (M.obj.map g.op z) = M.obj.map (f ≫ g).op z := by
  rw [op_comp, M.obj.map_comp]
  rfl

private theorem sectionCocycle_is_cech
    (c : (L ≃ₐ[K] L) → M.obj.obj (op (fieldObject K L)))
    (hc : ∀ σ τ, c (σ * τ) =
      M.obj.map (fieldAutomorphism K L σ).op (c τ) + c σ)
    (z : M.obj.obj (op (pairObject K L)))
    (hz : ∀ σ, M.obj.map (pairComponentArrow K L σ).op z = c σ) :
    M.obj.map (tripleThirdPair K L).op z - M.obj.map (tripleSecondPair K L).op z +
      M.obj.map (tripleFirstPair K L).op z = 0 := by
  apply tripleSections_ext K L M
  intro σ τ
  simp only [map_add, map_sub, map_zero, restrict_comp, tripleComponentArrow_firstPair,
    tripleComponentArrow_secondPair, tripleComponentArrow_thirdPair, hz]
  rw [← restrict_comp, hz, hc]
  abel

theorem injective_sections_HOne_subsingleton [Injective M] :
    Subsingleton (groupCohomology (sectionsRep K L M) 1) := by
  let A := sectionsRep K L M
  refine subsingleton_of_forall_eq 0 ?_
  intro a
  induction a using H1_induction_on with
  | h c =>
    apply (H1π_eq_zero_iff c).mpr
    let u : (L ≃ₐ[K] L) → M.obj.obj (op (fieldObject K L)) := c
    have hu : ∀ σ τ, u (σ * τ) =
        M.obj.map (fieldAutomorphism K L σ).op (u τ) + u σ :=
      (mem_cocycles₁_iff (A := A) (c : (L ≃ₐ[K] L) → A)).mp c.property
    let e := pairSectionsEquiv K L M
    let z := e.symm u
    have hz (σ : L ≃ₐ[K] L) : M.obj.map (pairComponentArrow K L σ).op z = u σ :=
      congrFun (e.apply_symm_apply u) σ
    have hδ := sectionCocycle_is_cech K L M u hu z hz
    let p {W : (X K).Etale} (s t : W ⟶ fieldObject K L) :
        M.obj.obj (op W) := M.obj.map (pairLift K L s t).op z
    have hn {W V : (X K).Etale} (r : V ⟶ W) (s t : W ⟶ fieldObject K L) :
        M.obj.map r.op (p s t) = p (r ≫ s) (r ≫ t) := by
      change M.obj.map r.op (M.obj.map (pairLift K L s t).op z) =
        M.obj.map (pairLift K L (r ≫ s) (r ≫ t)).op z
      rw [restrict_comp, comp_pairLift]
    have ha {W : (X K).Etale} (s t v : W ⟶ fieldObject K L) :
        p t v - p s v + p s t = 0 := by
      have hPull := congrArg (M.obj.map (tripleLift K L s t v).op) hδ
      simpa only [map_add, map_sub, map_zero, restrict_comp, tripleLift_firstPair,
        tripleLift_secondPair, tripleLift_thirdPair, p] using hPull
    obtain ⟨b, hb⟩ := InjectiveCechOne.exists_coboundary (J K) (fieldObject K L) M p hn ha
    refine ⟨b, ?_⟩
    funext σ
    have he : pairLift K L (𝟙 (fieldObject K L)) (fieldAutomorphism K L σ) =
        pairComponentArrow K L σ :=
      pairHom_ext K L ((pairLift_first K L _ _).trans (pairComponentArrow_first K L σ).symm)
        ((pairLift_second K L _ _).trans (pairComponentArrow_second K L σ).symm)
    have hb' := hb (𝟙 (fieldObject K L)) (fieldAutomorphism K L σ)
    change M.obj.map (pairLift K L _ _).op z = _ at hb'
    rw [he, hz] at hb'
    have hId : M.obj.map (𝟙 (fieldObject K L)).op b = b := by
      rw [show (𝟙 (fieldObject K L)).op = 𝟙 _ by rfl, M.obj.map_id]
      rfl
    rw [hId] at hb'
    exact hb'.symm

end
end ManuscriptAudit.GaloisCoverAction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.GaloisCoverAction.injective_sections_HOne_subsingleton
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
