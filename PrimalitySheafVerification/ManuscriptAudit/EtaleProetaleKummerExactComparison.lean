import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleKummerComparison

/-! Both actual Kummer sequences are exact in invertible degree on the same comparison. -/

namespace ManuscriptAudit.EtaleProetaleKummerExactComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open EtaleProetaleKummerComparison

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{0}
private abbrev B := AddCommGrpCat.{1}
private abbrev U : A ⥤ B := AddCommGrpCat.uliftFunctor.{1}

local instance etaleHasExt (X : Scheme.{0}) : HasExt.{1} (Sheaf X.smallEtaleTopology B) := by
  letI : EssentiallySmall.{1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology B
  exact IsGrothendieckAbelian.hasExt _

variable {K : Type} [Field K] {X : Scheme.{0}} (k : X ⟶ Spec (CommRingCat.of K))

private abbrev Jₐ (X : Scheme.{0}) := Scheme.AffineEtale.topology X
private abbrev q (X : Scheme.{0}) : Sheaf (Jₐ X) A ⥤ Sheaf (Jₐ X) B :=
  sheafCompose (Jₐ X) U
private abbrev p (X : Scheme.{0}) :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology B :=
  sheafCompose X.smallEtaleTopology U

include k in
private theorem lifted_affine_power_epi (d : ℕ) (hd : 0 < d) [NeZero (d : K)] :
    Epi ((q X).map (KummerSheafSequence.sequence X d).g) := by
  let f := KummerSheafSequence.sheafPower X d
  have hLoc : Presheaf.IsLocallySurjective (Jₐ X) (KummerUnitsPresheaf.power X d) := by
    apply KummerUnitsPresheaf.power_isLocallySurjective d hd
    intro W
    have hUnit : IsUnit (d : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
    simpa only [map_natCast] using hUnit.map (KummerRelativeCoefficients.coefficientMap k W)
  letI : Sheaf.IsLocallySurjective f :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff (Jₐ X)
      (KummerUnitsPresheaf.power X d)).mpr hLoc
  letI : Sheaf.IsLocallySurjective ((q X).map f) := by
    constructor
    intro W y
    refine (Jₐ X).superset_covering ?_ (Presheaf.imageSieve_mem (Jₐ X) f.hom y.down)
    intro V j hj
    obtain ⟨x, hx⟩ := hj
    exact ⟨ULift.up x, congrArg ULift.up hx⟩
  change Epi ((q X).map f)
  infer_instance

include k in
private theorem lifted_etale_power_epi (d : ℕ) (hd : 0 < d) [NeZero (d : K)] :
    Epi (etaleSequence X d).g := by
  let e₀ := Scheme.AffineEtale.sheafEquiv X A
  let e₁ := Scheme.AffineEtale.sheafEquiv X B
  let f := (KummerSheafSequence.sequence X d).g
  let F := q X
  haveI : Epi (F.map f) := lifted_affine_power_epi k d hd
  apply e₁.inverse.epi_of_epi_map
  change Epi (F.map (e₀.inverse.map (e₀.functor.map f)))
  let e := e₀.unitIso.app (KummerSheafSequence.sequence X d).X₂
  have hNat : f ≫ e.hom = e.hom ≫ e₀.inverse.map (e₀.functor.map f) :=
    e₀.unitIso.hom.naturality f
  have hEq : e₀.inverse.map (e₀.functor.map f) = e.inv ≫ f ≫ e.hom := by
    rw [hNat, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hEq, Functor.map_comp, Functor.map_comp]
  infer_instance

include k in
theorem etale_shortExact (d : ℕ) (hd : 0 < d) [NeZero (d : K)] :
    (etaleSequence X d).ShortExact := by
  let F := p X
  let P := sheafToPresheaf X.smallEtaleTopology B
  letI : PreservesFiniteLimits (F ⋙ P) := by
    change PreservesFiniteLimits (sheafToPresheaf X.smallEtaleTopology A ⋙
      (Functor.whiskeringRight X.Etaleᵒᵖ A B).obj U)
    infer_instance
  letI : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F P
  letI : F.Additive := Functor.additive_of_preserves_binary_products F
  let S := KummerRelativeFull.sequence X d
  have hS : S.ShortExact := KummerRelativeFull.sequence_shortExact k d hd
  have hKernel : IsLimit (KernelFork.ofι (etaleSequence X d).f (etaleSequence X d).zero) :=
    KernelFork.mapIsLimit _ hS.fIsKernel F
  have hExact := (etaleSequence X d).exact_of_f_is_kernel hKernel
  exact ShortComplex.ShortExact.mk' hExact (mono_of_isLimit_fork hKernel)
    (lifted_etale_power_epi k d hd)

include k in
theorem boundary_comparison_of_invertible_degree (d n : ℕ) [NeZero d] [NeZero (d : K)]
    [HasEnoughRootsOfUnity K d] (e : Sheaf.H (etaleSequence X d).X₃ n) :
    let hE := etale_shortExact k d (Nat.pos_of_ne_zero (NeZero.ne d))
    let hP := ProetaleKummerSequence.sequence_shortExact k d
    Sheaf.H.map (sequenceComparison X d).τ₁ (n+1)
      (EtaleProetaleCohomologyMap.pullback X (etaleSequence X d).X₁ (n+1)
        (e.comp hE.extClass rfl)) =
      (Sheaf.H.map (sequenceComparison X d).τ₃ n
        (EtaleProetaleCohomologyMap.pullback X (etaleSequence X d).X₃ n e)).comp hP.extClass rfl :=
  boundary_comparison X d n _ _ e

end
end ManuscriptAudit.EtaleProetaleKummerExactComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleKummerExactComparison.etale_shortExact,
      ``ManuscriptAudit.EtaleProetaleKummerExactComparison.boundary_comparison_of_invertible_degree] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
