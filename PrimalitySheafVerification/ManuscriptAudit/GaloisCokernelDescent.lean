import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FieldEtaleGaloisLocalLifts
import PrimalitySheafVerification.ManuscriptAudit.GaloisCoverAction
import PrimalitySheafVerification.ManuscriptAudit.GaloisOverlapLift
import PrimalitySheafVerification.ManuscriptAudit.GaloisOverlapSections
import PrimalitySheafVerification.ManuscriptAudit.GroupCohomologyBoundary
import PrimalitySheafVerification.ManuscriptAudit.SheafCoboundaryLift
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference

/-! Vanishing Galois H¹ with the actual coefficient sections descends a local lift. -/

namespace ManuscriptAudit.GaloisCoverAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FieldEtaleGaloisCovers GaloisTensorSquare
open GroupCohomologyBoundary SheafSectionDifference

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [Module.Finite K L] [IsGalois K L]

private abbrev X := Spec (CommRingCat.of K)
private abbrev J := (X K).smallEtaleTopology
private abbrev U := galoisObject K L
private abbrev T := terminalObject K
private abbrev f := galoisArrow K L

private theorem restrict_comp (M : Sheaf (J K) AddCommGrpCat.{0})
    {U₁ U₂ U₃ : (X K).Etale} (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) (z : M.obj.obj (op U₃)) :
    M.obj.map a.op (M.obj.map b.op z) = M.obj.map (a ≫ b).op z := by
  rw [op_comp, M.obj.map_comp]
  rfl

private theorem automorphism_over (σ : L ≃ₐ[K] L) :
    automorphism K L σ ≫ f K L = f K L :=
  MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w (automorphism K L σ))

theorem exists_global_cokernel_lift_of_HOne
    {F I : Sheaf (J K) AddCommGrpCat.{0}} (i : F ⟶ I) [Mono i]
    (hOne : Subsingleton (groupCohomology (sectionsRep K L F) 1))
    (x : (cokernel i).obj.obj (op (T K))) (y : I.obj.obj (op (U K L)))
    (hy : (cokernel.π i).hom.app (op (U K L)) y =
      (cokernel i).obj.map (f K L).op x) :
    ∃ z : I.obj.obj (op (T K)), (cokernel.π i).hom.app (op (T K)) z = x := by
  let W := U K L
  let q := cokernel.π i
  let j : F.obj.obj (op W) →+ I.obj.obj (op W) := (i.hom.app (op W)).hom
  have hEq (σ : L ≃ₐ[K] L) :
      q.hom.app (op W) (I.obj.map (automorphism K L σ).op y) = q.hom.app (op W) y := by
    rw [NatTrans.naturality_apply, hy, restrict_comp, automorphism_over]
  let c (σ : L ≃ₐ[K] L) : F.obj.obj (op W) :=
    difference i W (I.obj.map (automorphism K L σ).op y) y (hEq σ)
  have hc (σ : L ≃ₐ[K] L) : j (c σ) = I.obj.map (automorphism K L σ).op y - y :=
    difference_spec i W _ _ (hEq σ)
  have hCocycle (σ τ : L ≃ₐ[K] L) :
      c (σ * τ) = c σ + (sectionsRep K L F).ρ σ (c τ) := by
    apply section_injective i W
    change j (c (σ * τ)) = j (c σ + F.obj.map (automorphism K L σ).op (c τ))
    rw [j.map_add, hc (σ * τ)]
    have hn : j (F.obj.map (automorphism K L σ).op (c τ)) =
        I.obj.map (automorphism K L σ).op (j (c τ)) :=
      NatTrans.naturality_apply i.hom (automorphism K L σ).op (c τ)
    rw [hn, hc σ, hc τ, automorphism_mul,
      ← restrict_comp K L I (automorphism K L σ) (automorphism K L τ) y]
    rw [(I.obj.map (automorphism K L σ).op).hom.map_sub]
    abel
  obtain ⟨b, hb⟩ := exists_principal_cocycle_of_HOne_subsingleton
    (sectionsRep K L F) hOne c hCocycle
  let z := y - j b
  have hz (σ : L ≃ₐ[K] L) : I.obj.map (automorphism K L σ).op z = z := by
    have eq := hc σ
    have hn : j (F.obj.map (automorphism K L σ).op b) =
        I.obj.map (automorphism K L σ).op (j b) :=
      NatTrans.naturality_apply i.hom (automorphism K L σ).op b
    have hbσ := hb σ
    change c σ = F.obj.map (automorphism K L σ).op b - b at hbσ
    rw [hbσ, j.map_sub, hn] at eq
    change (I.obj.map (automorphism K L σ).op).hom (y - j b) = y - j b
    rw [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mpr eq.symm
  have hzq : q.hom.app (op W) z = (cokernel i).obj.map (f K L).op x := by
    have hn : q.hom.app (op W) (j b) = 0 :=
      (cokernel_sections_exact i W (j b)).2 ⟨b, rfl⟩
    change (q.hom.app (op W)).hom (y - j b) = _
    rw [map_sub]
    change q.hom.app (op W) y - q.hom.app (op W) (j b) = _
    rw [hy, hn, sub_zero]
  have hD : I.obj.map (pairFirst K L).op z = I.obj.map (pairSecond K L).op z := by
    apply (pairSectionsEquiv K L I).injective
    funext σ
    simp only [pairSectionsEquiv_apply, restrict_comp,
      pairComponentArrow_first, pairComponentArrow_second]
    have hId : I.obj.map (𝟙 (fieldObject K L)).op z = z := by simp
    exact hId.trans (hz σ).symm
  apply SheafH1Descent.exists_global_lift_of_compatible_cover (f K L)
    (galoisArrow_is_cover K L) q x z hzq
  intro D a b' _
  have hd := congrArg (I.obj.map (pairLift K L a b').op) hD
  simpa only [restrict_comp, pairLift_first, pairLift_second] using hd

end
end ManuscriptAudit.GaloisCoverAction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.GaloisCoverAction.exists_global_cokernel_lift_of_HOne
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
