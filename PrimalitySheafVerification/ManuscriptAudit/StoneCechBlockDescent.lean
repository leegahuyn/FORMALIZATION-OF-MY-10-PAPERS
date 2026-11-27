import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.StoneCechClopenBlocks
import PrimalitySheafVerification.ManuscriptAudit.StoneFiniteSectionExtension

/-! A continuous Čech cocycle that vanishes within each chosen block
descends on the compact closed images of the blocks, through the literal
topological quotient map on each fibre-pair subspace. -/

namespace ManuscriptAudit.StoneCechBlockDescent

open Set Topology
open StoneCechClopenBlocks (PairOver)

noncomputable section

variable {Y X D I : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
  [TopologicalSpace D] [DiscreteTopology D] [AddCommGroup D] [Finite D]

variable (p : C(Y, X)) (V : I → Set Y) (hV : ∀ i, IsClopen (V i))

abbrev blockImages (i : I) : Set X := p '' (V i)

include hV in
theorem blockImages_closed (i : I) : IsClosed (blockImages p V i) :=
  ((hV i).isClosed.isCompact.image p.continuous).isClosed

private abbrev BlockPairs (i j : I) : Set (Y × Y) :=
  (V i ×ˢ V j) ∩ {t | p t.1 = p t.2}

private def toPairs (i j : I) (t : BlockPairs p V i j) : PairOver p :=
  ⟨t.val, t.property.2⟩

private def toImageOverlap (i j : I) (t : BlockPairs p V i j) :
    blockImages p V i ∩ blockImages p V j :=
  ⟨p t.val.1, ⟨⟨t.val.1, t.property.1.1, rfl⟩,
    ⟨t.val.2, t.property.1.2, t.property.2.symm⟩⟩⟩

private theorem toImageOverlap_surjective (i j : I) :
    Function.Surjective (toImageOverlap p V i j) := by
  rintro ⟨x, ⟨⟨u, hu, he₁⟩, ⟨v, hv, he₂⟩⟩⟩
  exact ⟨⟨(u,v), ⟨⟨hu,hv⟩, he₁.trans he₂.symm⟩⟩, Subtype.ext he₁⟩

variable (c : C(PairOver p, D))
variable (cocycle : ∀ x y z (h₁ : p x = p y) (h₂ : p y = p z),
  c ⟨(x,y), h₁⟩ + c ⟨(y,z), h₂⟩ = c ⟨(x,z), h₁.trans h₂⟩)
variable (hZero : ∀ i u v (h : p u = p v), u ∈ V i → v ∈ V i → c ⟨(u,v),h⟩ = 0)

include cocycle hZero in
private theorem constant_on_fibres (i j : I) (u v : BlockPairs p V i j)
    (h : toImageOverlap p V i j u = toImageOverlap p V i j v) :
    c (toPairs p V i j u) = c (toPairs p V i j v) := by
  have hFirst : p u.val.1 = p v.val.1 := congrArg Subtype.val h
  have hSecond : p u.val.2 = p v.val.2 := u.property.2.symm.trans (hFirst.trans v.property.2)
  have h₁ := cocycle u.val.1 v.val.1 v.val.2 hFirst v.property.2
  have h₂ := cocycle u.val.1 u.val.2 v.val.2 u.property.2 hSecond
  rw [hZero i _ _ hFirst u.property.1.1 v.property.1.1, zero_add] at h₁
  rw [hZero j _ _ hSecond u.property.1.2 v.property.1.2, add_zero] at h₂
  exact h₂.trans h₁.symm

include hV cocycle hZero in
/-- The actual cocycle descends to the intersection of the two closed
block images and has a continuous extension to the ambient Stone space. -/
theorem exists_descent (i j : I) :
    ∃ q : C(X,D), ∀ x y (h : p x = p y), x ∈ V i → y ∈ V j →
      q (p x) = c ⟨(x,y),h⟩ := by
  classical
  have hClosed : IsClosed (BlockPairs p V i j) :=
    ((hV i).isClosed.prod (hV j).isClosed).inter
      (isClosed_eq (p.continuous.comp continuous_fst) (p.continuous.comp continuous_snd))
  letI : CompactSpace (BlockPairs p V i j) := isCompact_iff_compactSpace.mp hClosed.isCompact
  let r := toImageOverlap p V i j
  have hrC : Continuous r :=
    (p.continuous.comp continuous_subtype_val.fst).subtype_mk _
  have hq : IsQuotientMap r :=
    IsQuotientMap.of_surjective_continuous (toImageOverlap_surjective p V i j) hrC
  choose u hu using toImageOverlap_surjective p V i j
  let D₀ := blockImages p V i ∩ blockImages p V j
  let b : D₀ → D := fun z ↦ c (toPairs p V i j (u z))
  have hb : b ∘ r = fun t ↦ c (toPairs p V i j t) := by
    funext t
    exact constant_on_fibres p V c cocycle hZero i j (u (r t)) t (hu (r t))
  have hbC : Continuous b := by
    apply hq.continuous_iff.mpr
    rw [hb]
    exact c.continuous.comp (continuous_subtype_val.subtype_mk _)
  obtain ⟨a, ha⟩ := StoneFiniteSectionExtension.exists_extension D₀
    ((blockImages_closed p V hV i).inter (blockImages_closed p V hV j)) ⟨b, hbC⟩
  refine ⟨a, fun x y h hx hy ↦ ?_⟩
  let t : BlockPairs p V i j := ⟨(x,y), ⟨⟨hx,hy⟩,h⟩⟩
  change a (r t).val = c (toPairs p V i j t)
  exact (ha (r t)).trans (congrFun hb t)

end
end ManuscriptAudit.StoneCechBlockDescent

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.StoneCechBlockDescent.exists_descent
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
