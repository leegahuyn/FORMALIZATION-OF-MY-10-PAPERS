import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PointCoefficientDerived

/-! Exact stalks of the genuine point-coefficient sheaf at isolated support points. -/

namespace ManuscriptAudit.PointCoefficientStalk

open CategoryTheory Opposite TopologicalSpace Set
open ClosedSupportDetection PointCoefficientSheaf PointCoefficientDerived

noncomputable section

variable {X : TopCat.{0}} (P : Set X) (A : P → Type)
variable [∀ p : P, AddCommGroup (A p)]

private abbrev G := AddCommGrpCat.{0}

private def evaluate (V : Opens X) (p : P) (hp : p.val ∈ V) :
    Sections P A V →+ A p where
  toFun s := s ⟨p, hp⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem evaluate_bijective (V : Opens X) (p : P) (hp : p.val ∈ V)
    (hOnly : ∀ q : P, q.val ∈ V → q = p) :
    Function.Bijective (evaluate P A V p hp) := by
  constructor
  · intro s t h
    funext q
    obtain ⟨q, hq⟩ := q
    have he := hOnly q hq
    subst q
    exact h
  · intro a
    refine ⟨fun q => cast (congrArg A (hOnly q.val q.property).symm) a, ?_⟩
    change cast (congrArg A (hOnly p hp).symm) a = a
    rfl

private def germHom (V : Opens X) (p : P) (hp : p.val ∈ V) :
    Sections P A V →+ TopCat.Presheaf.stalk (C := G) (presheaf P A) p.val :=
  ((presheaf P A).germ V p.val hp).hom

private theorem germ_bijective (V : Opens X) (p : P) (hp : p.val ∈ V)
    (hOnly : ∀ q : P, q.val ∈ V → q = p) :
    Function.Bijective (germHom P A V p hp) := by
  let F := presheaf P A
  constructor
  · intro s t h
    change F.germ V p.val hp s = F.germ V p.val hp t at h
    obtain ⟨W, hpW, i, j, hst⟩ := F.germ_eq p.val hp hp s t h
    change restrict P A i.le s = restrict P A j.le t at hst
    have he := congrFun hst (⟨p, hpW⟩ : PointsIn P W)
    change s ⟨p, hp⟩ = t ⟨p, hp⟩ at he
    exact (evaluate_bijective P A V p hp hOnly).1 he
  · intro t
    obtain ⟨U, hUV, hpU, s, hs⟩ := F.exists_le_germ_eq (x := p.val) t hp
    obtain ⟨v, hv⟩ := restriction_surjective P A hUV s
    refine ⟨v, ?_⟩
    have he := F.germ_res_apply (homOfLE hUV) p.val hpU v
    change F.germ U p.val hpU (restrict P A hUV v) = F.germ V p.val hp v at he
    rw [hv] at he
    exact he.symm.trans hs

/-- In any neighborhood meeting the support in a single point, the stalk
at that point is exactly its designated coefficient. -/
def stalkEquivOfIsolation (V : Opens X) (p : P) (hp : p.val ∈ V)
    (hOnly : ∀ q : P, q.val ∈ V → q = p) :
    TopCat.Presheaf.stalk (C := G) (presheaf P A) p.val ≃+ A p :=
  (AddEquiv.ofBijective (germHom P A V p hp) (germ_bijective P A V p hp hOnly)).symm.trans
    (AddEquiv.ofBijective (evaluate P A V p hp) (evaluate_bijective P A V p hp hOnly))

private theorem exists_isolating_open [Finite P] (p : P)
    (hPoint : ∀ x ∈ P, IsClosed ({x} : Set X)) :
    ∃ V : Opens X, p.val ∈ V ∧ (∀ q : P, q.val ∈ V → q = p) := by
  classical
  let S (q : P) : Set X := if q = p then ∅ else {q.val}
  have hC : IsClosed (⋃ q : P, S q) := by
    apply isClosed_iUnion_of_finite
    intro q
    by_cases h : q = p
    · simpa [S, h] using (isClosed_empty : IsClosed (∅ : Set X))
    · simpa [S, h] using hPoint q.val q.property
  refine ⟨⟨(⋃ q : P, S q)ᶜ, hC.isOpen_compl⟩, ?_, ?_⟩
  · change p.val ∉ ⋃ q : P, S q
    intro h
    obtain ⟨q, hq⟩ := mem_iUnion.mp h
    by_cases e : q = p
    · simp [S, e] at hq
    · have he : p.val = q.val := by simpa [S, e] using hq
      exact e (Subtype.ext he.symm)
  · intro q hq
    change q.val ∉ ⋃ w : P, S w at hq
    by_contra hn
    exact hq (mem_iUnion.mpr ⟨q, by simp [S, hn]⟩)

/-- Finite closed supports have the prescribed stalk group at every point. -/
def stalkEquiv [Finite P] (p : P) (hPoint : ∀ x ∈ P, IsClosed ({x} : Set X)) :
    TopCat.Presheaf.stalk (C := G) (presheaf P A) p.val ≃+ A p :=
  let h := exists_isolating_open P p hPoint
  stalkEquivOfIsolation P A h.choose p h.choose_spec.1 h.choose_spec.2

theorem stalkSupport_eq [Finite P] [∀ p : P, Nontrivial (A p)]
    (hP : IsClosed P) (hPoint : ∀ x ∈ P, IsClosed ({x} : Set X)) :
    stalkSupport (sheaf P A) = P := by
  apply subset_antisymm (stalkSupport_subset P A hP)
  intro x hx
  let p : P := ⟨x, hx⟩
  let e := stalkEquiv P A p hPoint
  obtain ⟨a, b, hab⟩ := exists_pair_ne (A p)
  change Nontrivial (TopCat.Presheaf.stalk (C := G) (presheaf P A) x)
  exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective h)⟩

end
end ManuscriptAudit.PointCoefficientStalk

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PointCoefficientStalk.stalkEquivOfIsolation,
      ``ManuscriptAudit.PointCoefficientStalk.stalkEquiv,
      ``ManuscriptAudit.PointCoefficientStalk.stalkSupport_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
