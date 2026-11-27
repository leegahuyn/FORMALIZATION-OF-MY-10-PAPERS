import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.SheafCokernelBoundary
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenCokernelLift

/-! An integer order character on a two-open intersection detects any
torsion in degree-one cohomology, via actual lifts and differences. -/

namespace ManuscriptAudit.TwoOpenCohomologyNoTorsion

open CategoryTheory CategoryTheory.Limits Opposite
open TwoOpenCokernelLift (coverObjects coverArrows)
open SheafCokernelBoundary

universe u v w w'
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {F I : Sheaf J AddCommGrpCat.{w}} (i : F ⟶ I) [Mono i] [Injective I]

private theorem restrict_restrict (A : Sheaf J AddCommGrpCat.{w}) {X Y Z : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (x : A.obj.obj (op Z)) :
    A.obj.map a.op (A.obj.map b.op x) = A.obj.map (a ≫ b).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

set_option maxHeartbeats 2200000 in
/-- If order zero is exactly extension from the first chart and both
actual chart restrictions have order zero, positive multiples kill
no nonzero global degree-one classes. -/
theorem eq_zero_of_nsmul_eq_zero {T U V D : C} (hT : IsTerminal T)
    (u : U ⟶ T) (v : V ⟶ T) [Mono u] [Mono v]
    (p : D ⟶ U) (q : D ⟶ V) (hD : IsPullback p q u v)
    (hCover : Sieve.ofArrows (coverObjects U V) (coverArrows u v) ∈ J T)
    (ρ : F.obj.obj (op D) →+ ℤ)
    (hExact : Function.Exact (F.obj.map p.op) ρ)
    (hV : ∀ z : F.obj.obj (op V), ρ (F.obj.map q.op z) = 0)
    (hLiftU : Function.Surjective ((cokernel.π i).hom.app (op U)))
    (hLiftV : Function.Surjective ((cokernel.π i).hom.app (op V)))
    {n : ℕ} (hn : 0 < n) (α : Sheaf.H F 1) (hα : n • α = 0) : α = 0 := by
  let Q := cokernel i
  let π : I ⟶ Q := cokernel.π i
  let δ := boundary i hT
  obtain ⟨x, hx⟩ := SheafH1Descent.connectingSection_surjective i hT α
  have hx' : δ x = α := hx
  have hnx : δ (n • x) = 0 := by rw [map_nsmul, hx']; exact hα
  obtain ⟨z, hz⟩ := (boundary_eq_zero_iff i hT (n • x)).mp hnx
  obtain ⟨a, ha⟩ := hLiftU (Q.obj.map u.op x)
  obtain ⟨b, hb⟩ := hLiftV (Q.obj.map v.op x)
  have he : π.hom.app (op D) (I.obj.map p.op a) = π.hom.app (op D) (I.obj.map q.op b) := by
    rw [NatTrans.naturality_apply π.hom p.op a, NatTrans.naturality_apply π.hom q.op b, ha, hb,
      restrict_restrict, restrict_restrict, hD.w]
  obtain ⟨c, hc, _⟩ := SheafSectionDifference.existsUnique_difference i D
    (I.obj.map p.op a) (I.obj.map q.op b) he
  have hLocal {W : C} (f : W ⟶ T) (y : I.obj.obj (op W))
      (hy : π.hom.app (op W) y = Q.obj.map f.op x) :
      ∃ s : F.obj.obj (op W), i.hom.app (op W) s = n • y - I.obj.map f.op z := by
    apply (SheafSectionDifference.cokernel_sections_exact i W _).mp
    change (π.hom.app (op W)).hom (n • y - I.obj.map f.op z) = 0
    rw [map_sub, map_nsmul]
    change n • π.hom.app (op W) y - π.hom.app (op W) (I.obj.map f.op z) = 0
    rw [hy, NatTrans.naturality_apply π.hom f.op z, hz]
    change n • Q.obj.map f.op x - (Q.obj.map f.op).hom (n • x) = 0
    rw [map_nsmul, sub_self]
  obtain ⟨s, hs⟩ := hLocal u a ha
  obtain ⟨t, ht⟩ := hLocal v b hb
  have hcmul : n • c = F.obj.map p.op s - F.obj.map q.op t := by
    apply SheafSectionDifference.section_injective i D
    change (i.hom.app (op D)).hom (n • c) =
      (i.hom.app (op D)).hom (F.obj.map p.op s - F.obj.map q.op t)
    rw [map_nsmul, map_sub]
    change n • i.hom.app (op D) c =
      i.hom.app (op D) (F.obj.map p.op s) - i.hom.app (op D) (F.obj.map q.op t)
    rw [NatTrans.naturality_apply i.hom p.op s, NatTrans.naturality_apply i.hom q.op t, hs, ht, hc]
    change n • (I.obj.map p.op a - I.obj.map q.op b) =
      (I.obj.map p.op).hom (n • a - I.obj.map u.op z) -
        (I.obj.map q.op).hom (n • b - I.obj.map v.op z)
    rw [map_sub, map_sub, map_nsmul, map_nsmul]
    have hSame : I.obj.map p.op (I.obj.map u.op z) = I.obj.map q.op (I.obj.map v.op z) := by
      rw [restrict_restrict, restrict_restrict, hD.w]
    rw [hSame, nsmul_sub]
    abel
  have hOrdU : ρ (F.obj.map p.op s) = 0 :=
    (hExact _).mpr ⟨s, rfl⟩
  have hOrd : (n : ℤ) * ρ c = 0 := by
    have hh := congrArg ρ hcmul
    simpa only [map_nsmul, map_sub, hOrdU, hV t, sub_self, nsmul_eq_mul] using hh
  have hcast : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hzero : ρ c = 0 := (mul_eq_zero.mp hOrd).resolve_left hcast
  obtain ⟨r, hr⟩ := (hExact c).mp hzero
  have hl := TwoOpenCokernelLift.exists_global_lift_of_difference i u v p q hD hCover
    x a b ha hb c hc r hr
  exact hx'.symm.trans ((boundary_eq_zero_iff i hT x).mpr hl)

end
end ManuscriptAudit.TwoOpenCohomologyNoTorsion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.TwoOpenCohomologyNoTorsion.eq_zero_of_nsmul_eq_zero
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
