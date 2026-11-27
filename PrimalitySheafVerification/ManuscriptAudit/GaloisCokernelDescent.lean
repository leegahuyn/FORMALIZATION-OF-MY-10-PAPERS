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

def terminalObject_isTerminal : IsTerminal (T K) :=
  IsTerminal.ofUniqueHom
    (fun U => MorphismProperty.Over.homMk U.hom (Category.comp_id _))
    (fun U a => MorphismProperty.Over.Hom.ext (by
      have h := MorphismProperty.Over.w a
      change a.left ≫ 𝟙 (X K) = U.hom at h
      rwa [Category.comp_id] at h))

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
      c (σ * τ) = c σ + F.obj.map (automorphism K L σ).op (c τ) := by
    apply section_injective i W
    change j (c (σ * τ)) = j (c σ + F.obj.map (automorphism K L σ).op (c τ))
    rw [j.map_add, hc (σ * τ)]
    have hn : j (F.obj.map (automorphism K L σ).op (c τ)) =
        I.obj.map (automorphism K L σ).op (j (c τ)) :=
      NatTrans.naturality_apply i.hom (automorphism K L σ).op (c τ)
    rw [hn, hc σ, hc τ, automorphism_mul,
      ← restrict_comp K I (automorphism K L σ) (automorphism K L τ) y]
    rw [(I.obj.map (automorphism K L σ).op).hom.map_sub]
    abel
  obtain ⟨bRep, hbRep⟩ := exists_principal_cocycle_of_HOne_subsingleton
    (sectionsRep K L F) hOne (fun σ => c σ) (fun σ τ => hCocycle σ τ)
  let b : F.obj.obj (op W) := bRep
  have hb (σ : L ≃ₐ[K] L) : c σ = F.obj.map (automorphism K L σ).op b - b :=
    hbRep σ
  let z := y - j b
  have hz (σ : L ≃ₐ[K] L) : I.obj.map (automorphism K L σ).op z = z := by
    have eq := hc σ
    have hn : j (F.obj.map (automorphism K L σ).op b) =
        I.obj.map (automorphism K L σ).op (j b) :=
      NatTrans.naturality_apply i.hom (automorphism K L σ).op b
    rw [hb σ, j.map_sub, hn] at eq
    let g := (I.obj.map (automorphism K L σ).op).hom
    change g (y - j b) = y - j b
    rw [map_sub]
    change g (j b) - j b = g y - y at eq
    calc
      g y - g (j b) = (g y - y) - (g (j b) - j b) + (y - j b) := by abel
      _ = _ := by rw [← eq, sub_self, zero_add]
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
    rw [pairSectionsEquiv_apply, pairSectionsEquiv_apply]
    change I.obj.map (pairComponentArrow K L σ).op (I.obj.map (pairFirst K L).op z) =
      I.obj.map (pairComponentArrow K L σ).op (I.obj.map (pairSecond K L).op z)
    rw [restrict_comp K I (pairComponentArrow K L σ) (pairFirst K L) z,
      restrict_comp K I (pairComponentArrow K L σ) (pairSecond K L) z,
      pairComponentArrow_first, pairComponentArrow_second]
    have hId : I.obj.map (𝟙 (fieldObject K L)).op z = z := by
      rw [show (𝟙 (fieldObject K L)).op = 𝟙 _ by rfl, I.obj.map_id]
      rfl
    exact hId.trans (hz σ).symm
  apply SheafH1Descent.exists_global_lift_of_compatible_cover (f K L)
    (galoisArrow_is_cover K L) q x z hzq
  intro D a b' _
  let a' : D ⟶ fieldObject K L := a
  let b'' : D ⟶ fieldObject K L := b'
  let e := pairLift K L a' b''
  let res (u : D ⟶ fieldObject K L) : I.obj.obj (op D) := I.obj.map u.op z
  change res a' = res b''
  calc
    res a' = res (e ≫ pairFirst K L) :=
      (congrArg res (pairLift_first K L a' b'')).symm
    _ = I.obj.map e.op (I.obj.map (pairFirst K L).op z) :=
      (restrict_comp K I e (pairFirst K L) z).symm
    _ = I.obj.map e.op (I.obj.map (pairSecond K L).op z) :=
      congrArg (I.obj.map e.op) hD
    _ = res (e ≫ pairSecond K L) := restrict_comp K I e (pairSecond K L) z
    _ = res b'' := congrArg res (pairLift_second K L a' b'')

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
