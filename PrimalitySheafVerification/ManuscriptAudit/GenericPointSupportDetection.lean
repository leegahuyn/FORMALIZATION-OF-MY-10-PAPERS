import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import PrimalitySheafVerification.ManuscriptAudit.ClosedSupportDetection

/-!
# Stalk support at a generic point

A section representing a nonzero generic germ forces every stalk on its
domain to be nonzero. In Spec ℤ, every generic neighborhood also contains
a nonzero prime. In particular, no abelian sheaf has exactly the generic
singleton as its stalk support.
-/

namespace ManuscriptAudit.GenericPointSupportDetection

open CategoryTheory Opposite TopologicalSpace
open ManuscriptAudit.ClosedSupportDetection

noncomputable section

private abbrev G := AddCommGrpCat.{0}

/-- A nonzero stalk at a point specializing to every point forces the support
to contain an open neighborhood of that point. -/
theorem exists_open_subset_support {X : TopCat.{0}} (F : AbelianSheaf X)
    {η : X} (hgen : ∀ x : X, Specializes η x) (hη : η ∈ stalkSupport F) :
    ∃ U : Opens X, η ∈ U ∧ (U : Set X) ⊆ stalkSupport F := by
  letI : Nontrivial (TopCat.Presheaf.stalk (C := G) F.obj η) := hη
  obtain ⟨a, ha⟩ := exists_ne (0 : TopCat.Presheaf.stalk (C := G) F.obj η)
  obtain ⟨U, hηU, s, hs⟩ := TopCat.Presheaf.exists_germ_eq (C := G) F.obj a
  refine ⟨U, hηU, ?_⟩
  intro x hx
  have hxU : x ∈ U := hx
  have hnz : TopCat.Presheaf.germ F.obj U x hxU s ≠ 0 := by
    intro hzero
    have h := DFunLike.congr_fun (TopCat.Presheaf.germ_stalkSpecializes F.obj hxU (hgen x)) s
    change (TopCat.Presheaf.stalkSpecializes F.obj (hgen x)) (TopCat.Presheaf.germ F.obj U x hxU s) =
      TopCat.Presheaf.germ F.obj U η ((hgen x).mem_open U.isOpen hxU) s at h
    rw [hzero, map_zero] at h
    apply ha
    rw [← hs]
    exact h.symm
  change Nontrivial (TopCat.Presheaf.stalk (C := G) F.obj x)
  exact ⟨⟨_, 0, hnz⟩⟩

private theorem basicOpen_contains_nonzero_prime (n : ℤ) (hn : n ≠ 0) :
    ∃ x : PrimeSpectrum ℤ, x ∈ PrimeSpectrum.basicOpen n ∧ x ≠ ⊥ := by
  obtain ⟨p, hpLarge, hp⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
  letI : Fact p.Prime := ⟨hp⟩
  let f := Int.castRingHom (ZMod p)
  let x := PrimeSpectrum.comap f (⊥ : PrimeSpectrum (ZMod p))
  refine ⟨x, ?_, ?_⟩
  · change ¬ (((n : ℤ) : ZMod p) ∈ (⊥ : Ideal (ZMod p)))
    rw [Ideal.mem_bot]
    intro hz
    have hdiv : (p : ℤ) ∣ n := (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp hz
    have hNat : p ∣ n.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdiv)
    have hsmall : p ≤ n.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hNat
    exact (Nat.not_succ_le_self n.natAbs) (hpLarge.trans hsmall)
  · intro hx
    have hm : (p : ℤ) ∈ x.asIdeal := by
      change (((p : ℤ) : ZMod p) ∈ (⊥ : Ideal (ZMod p)))
      rw [Ideal.mem_bot, ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [hx, PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] at hm
    exact hp.ne_zero (by simpa using hm)

/-- Every open neighborhood of the generic point in Spec ℤ contains a nonzero prime. -/
theorem specInt_neighborhood_contains_nonzero_prime (U : Opens (PrimeSpectrum ℤ))
    (hη : (⊥ : PrimeSpectrum ℤ) ∈ U) :
    ∃ x : PrimeSpectrum ℤ, x ∈ U ∧ x ≠ ⊥ := by
  obtain ⟨_, ⟨n, rfl⟩, hn, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hη U.isOpen
  have hn' : n ≠ 0 := by
    simpa only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] using hn
  obtain ⟨x, hx, hne⟩ := basicOpen_contains_nonzero_prime n hn'
  exact ⟨x, hsub hx, hne⟩

private theorem basicOpen_compl_finite (n : ℤ) (hn : n ≠ 0) :
    ((PrimeSpectrum.basicOpen n : Set (PrimeSpectrum ℤ))ᶜ).Finite := by
  let I : Ideal ℤ := Ideal.span {n}
  letI : NeZero n := ⟨hn⟩
  letI : Finite (ℤ ⧸ I) := by
    dsimp [I]
    infer_instance
  letI : Finite (PrimeSpectrum (ℤ ⧸ I)) :=
    Finite.of_injective (fun x : PrimeSpectrum (ℤ ⧸ I) => (x.asIdeal : Set (ℤ ⧸ I)))
      (fun _ _ h => PrimeSpectrum.ext_iff.mpr (SetLike.coe_injective h))
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl]
  have h := Set.finite_range (PrimeSpectrum.comap (Ideal.Quotient.mk I))
  simpa only [range_comap_of_surjective (ℤ ⧸ I) (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective, Ideal.mk_ker, I, PrimeSpectrum.zeroLocus_span] using h

/-- An open neighborhood of the generic point of Spec ℤ has finite complement. -/
theorem specInt_generic_neighborhood_compl_finite (U : Opens (PrimeSpectrum ℤ))
    (hη : (⊥ : PrimeSpectrum ℤ) ∈ U) :
    ((U : Set (PrimeSpectrum ℤ))ᶜ).Finite := by
  obtain ⟨_, ⟨n, rfl⟩, hn, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hη U.isOpen
  have hn' : n ≠ 0 := by
    simpa only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] using hn
  exact (basicOpen_compl_finite n hn').subset (Set.compl_subset_compl.mpr hsub)

/-- Any stalk support containing the generic point of Spec ℤ has finite complement. -/
theorem specInt_stalkSupport_compl_finite_of_generic_mem
    (F : AbelianSheaf (TopCat.of (PrimeSpectrum ℤ)))
    (hη : (⊥ : PrimeSpectrum ℤ) ∈ stalkSupport F) :
    ((stalkSupport F)ᶜ).Finite := by
  have hgen : ∀ x : PrimeSpectrum ℤ, Specializes (⊥ : PrimeSpectrum ℤ) x := by
    intro x
    exact (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨U, hηU, hU⟩ := exists_open_subset_support F hgen hη
  exact (specInt_generic_neighborhood_compl_finite U hηU).subset (Set.compl_subset_compl.mpr hU)

/-- The generic singleton of Spec ℤ is not the exact support of any abelian sheaf. -/
theorem specInt_stalkSupport_ne_generic_singleton
    (F : AbelianSheaf (TopCat.of (PrimeSpectrum ℤ))) :
    stalkSupport F ≠ ({(⊥ : PrimeSpectrum ℤ)} : Set (PrimeSpectrum ℤ)) := by
  intro hF
  have hgen : ∀ x : PrimeSpectrum ℤ, Specializes (⊥ : PrimeSpectrum ℤ) x := by
    intro x
    exact (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  have hη : (⊥ : PrimeSpectrum ℤ) ∈ stalkSupport F := by rw [hF]; simp
  obtain ⟨U, hηU, hU⟩ := exists_open_subset_support F hgen hη
  obtain ⟨x, hxU, hxne⟩ := specInt_neighborhood_contains_nonzero_prime U hηU
  have hx : x ∈ stalkSupport F := hU hxU
  rw [hF, Set.mem_singleton_iff] at hx
  exact hxne hx

end

end ManuscriptAudit.GenericPointSupportDetection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.GenericPointSupportDetection.exists_open_subset_support,
      ``ManuscriptAudit.GenericPointSupportDetection.specInt_neighborhood_contains_nonzero_prime,
      ``ManuscriptAudit.GenericPointSupportDetection.specInt_generic_neighborhood_compl_finite,
      ``ManuscriptAudit.GenericPointSupportDetection.specInt_stalkSupport_compl_finite_of_generic_mem,
      ``ManuscriptAudit.GenericPointSupportDetection.specInt_stalkSupport_ne_generic_singleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
