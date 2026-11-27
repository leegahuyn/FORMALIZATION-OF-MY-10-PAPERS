import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.EpiMono
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

private abbrev p (X : Scheme.{0}) :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology B :=
  sheafCompose X.smallEtaleTopology U

include k in
private theorem lifted_etale_power_epi (d : ℕ) (hd : 0 < d) [NeZero (d : K)] :
    Epi (etaleSequence X d).g := by
  let J := X.smallEtaleTopology
  let f := (KummerRelativeFull.sequence X d).g
  have hf : Epi f := (KummerRelativeFull.sequence_shortExact k d hd).epi_g
  letI : Sheaf.IsLocallySurjective f :=
    (Sheaf.isLocallySurjective_iff_epi' A f).mpr hf
  letI : Sheaf.IsLocallySurjective ((p X).map f) := by
    constructor
    intro W y
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J f.hom y.down)
    intro V g hg
    obtain ⟨x, hx⟩ := hg
    exact ⟨ULift.up x, congrArg ULift.up hx⟩
  change Epi ((p X).map f)
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
