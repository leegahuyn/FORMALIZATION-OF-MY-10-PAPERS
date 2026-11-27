import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.EpiMono
import PrimalitySheafVerification.ManuscriptAudit.ClosedSupportDetection
import PrimalitySheafVerification.ManuscriptAudit.PointCoefficientSheaf
import PrimalitySheafVerification.ManuscriptAudit.SheafPointwiseKernel

/-! Point-coefficient sheaves take coefficientwise short exactness to native short exactness. -/

namespace ManuscriptAudit.PointCoefficientExact

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PointCoefficientSheaf ClosedSupportDetection

noncomputable section

variable {X : TopCat.{0}} (P : Set X)

private abbrev G := AddCommGrpCat.{0}

abbrev coefficientSheaf (A : P → G) : AbelianSheaf X := sheaf P (fun p => A p)

def coefficientMap {A B : P → G} (f : ∀ p, A p ⟶ B p) :
    coefficientSheaf P A ⟶ coefficientSheaf P B :=
  ⟨{ app := fun U => AddCommGrpCat.ofHom
      { toFun := fun s q => f q.val (s q)
        map_zero' := by funext q; simp
        map_add' := by intro s t; funext q; simp }
     naturality := by
       intro U V g
       apply ConcreteCategory.hom_ext
       intro s
       rfl }⟩

def coefficientSequence (S : P → ShortComplex G) : ShortComplex (AbelianSheaf X) :=
  ShortComplex.mk (coefficientMap P (fun p => (S p).f)) (coefficientMap P (fun p => (S p).g))
    (by
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply ConcreteCategory.hom_ext
      intro s
      funext q
      change (S q.val).g ((S q.val).f (s q)) = 0
      exact ConcreteCategory.congr_hom (S q.val).zero (s q))

theorem app_f_injective (S : P → ShortComplex G) (hS : ∀ p, (S p).ShortExact)
    (U : (Opens X)ᵒᵖ) : Function.Injective ((coefficientSequence P S).f.hom.app U) := by
  intro s t h
  funext q
  letI : Mono (S q.val).f := (hS q.val).mono_f
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance (congrFun h q)

theorem app_g_surjective (S : P → ShortComplex G) (hS : ∀ p, (S p).ShortExact)
    (U : (Opens X)ᵒᵖ) : Function.Surjective ((coefficientSequence P S).g.hom.app U) := by
  intro t
  have hs (q : PointsIn P U.unop) : ∃ s : (S q.val).X₂, (S q.val).g s = t q := by
    letI : Epi (S q.val).g := (hS q.val).epi_g
    exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance (t q)
  refine ⟨fun q => (hs q).choose, ?_⟩
  funext q
  exact (hs q).choose_spec

theorem app_exact (S : P → ShortComplex G) (hS : ∀ p, (S p).ShortExact) (U : (Opens X)ᵒᵖ) :
    Function.Exact ((coefficientSequence P S).f.hom.app U) ((coefficientSequence P S).g.hom.app U) := by
  intro t
  constructor
  · intro ht
    have hs (q : PointsIn P U.unop) : ∃ s : (S q.val).X₁, (S q.val).f s = t q := by
      have hx := (ShortComplex.ab_exact_iff_function_exact _).mp (hS q.val).exact
      exact (hx (t q)).mp (congrFun ht q)
    refine ⟨fun q => (hs q).choose, ?_⟩
    funext q
    exact (hs q).choose_spec
  · rintro ⟨s, rfl⟩
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.hom.app U) (coefficientSequence P S).zero) s

theorem coefficientSequence_shortExact (S : P → ShortComplex G) (hS : ∀ p, (S p).ShortExact) :
    (coefficientSequence P S).ShortExact := by
  let Q := coefficientSequence P S
  have hK := SheafPointwiseKernel.kernel_isLimit Q (app_f_injective P S hS) (app_exact P S hS)
  letI : Mono Q.f := mono_of_isLimit_fork hK
  let U := TopCat.Sheaf.forget G X
  letI : Epi (U.map Q.g) :=
    (NatTrans.epi_iff_epi_app _).mpr fun V =>
      (AddCommGrpCat.epi_iff_surjective _).mpr (app_g_surjective P S hS V)
  letI : Epi Q.g := by
    constructor
    intro T f g h
    apply U.map_injective
    apply (cancel_epi (U.map Q.g)).mp
    calc
      _ = U.map (Q.g ≫ f) := (U.map_comp Q.g f).symm
      _ = U.map (Q.g ≫ g) := congrArg (fun j => U.map j) h
      _ = _ := U.map_comp Q.g g
  exact { exact := Q.exact_of_f_is_kernel hK }

end
end ManuscriptAudit.PointCoefficientExact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PointCoefficientExact.app_f_injective,
      ``ManuscriptAudit.PointCoefficientExact.app_g_surjective,
      ``ManuscriptAudit.PointCoefficientExact.app_exact,
      ``ManuscriptAudit.PointCoefficientExact.coefficientSequence_shortExact] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
