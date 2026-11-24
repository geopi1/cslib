/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Cslib.Foundations.Relation.Confluence

/-! # β-confluence for the λ-calculus

Confluence of full β-reduction is proved via parallel reduction `⭢ₚ`, whose diamond property follows
from Takahashi's triangle property for complete developments (`para_dev_triangle`).

## References

* [M. Takahashi, *Parallel reductions in λ-calculus*][Takahashi1995]
-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation

/-- A parallel β-reduction step. -/
@[reduction_sys "ₚ"]
inductive Parallel : Term Var → Term Var → Prop
/-- Free variables parallel step to themselves. -/
| fvar (x : Var) : Parallel (fvar x) (fvar x)
/-- A parallel left and right congruence rule for application. -/
| app : Parallel L L' → Parallel M M' → Parallel (app L M) (app L' M')
/-- Congruence rule for lambda terms. -/
| abs (xs : Finset Var) :
    (∀ x ∉ xs, Parallel (m ^ fvar x) (m' ^ fvar x)) → Parallel (abs m) (abs m')
/-- A parallel β-reduction. -/
| beta (xs : Finset Var) :
    (∀ x ∉ xs, Parallel (m ^ fvar x) (m' ^ fvar x) ) →
    Parallel n n' →
    Parallel (app (abs m) n) (m' ^ n')

open Parallel

attribute [scoped grind .] Parallel.fvar Parallel.app
attribute [scoped grind cases] Parallel

variable {M M' N N' : Term Var}

/-- The left side of a parallel reduction is locally closed. -/
@[scoped grind →]
lemma para_lc_l (step : M ⭢ₚ N) : LC M  := by
  induction step
  case abs _ _ xs _ ih => exact LC.abs xs _ ih
  case beta => refine LC.app (LC.abs ?_ _ ?_) ?_ <;> assumption
  all_goals grind

/-- Parallel reduction is reflexive for locally closed terms. -/
@[scoped grind →]
lemma Parallel.lc_refl (M : Term Var) (lc : LC M) : M ⭢ₚ M := by
  induction lc
  all_goals constructor <;> assumption

variable [HasFresh Var] [DecidableEq Var]

/-- The right side of a parallel reduction is locally closed. -/
@[scoped grind →]
lemma para_lc_r (step : M ⭢ₚ N) : LC N := by
  induction step
  case abs _ _ xs _ ih => exact LC.abs xs _ ih
  case beta => refine beta_lc (LC.abs ?_ _ ?_) ?_ <;> assumption
  all_goals grind

omit [HasFresh Var] [DecidableEq Var] in
/-- The inclusion `(· ⭢βᶠ ·) ≤ (· ⭢ₚ ·)`. -/
lemma FullBeta.le_parallel :
    ((· ⭢βᶠ ·) : Term Var → Term Var → Prop) ≤ (· ⭢ₚ ·) := by
  intro M N step
  induction step with
  | base h =>
    cases h with | beta abs_lc _ =>
    cases abs_lc with | abs xs _ =>
    apply Parallel.beta xs <;> grind
  | abs xs _ _ => apply Parallel.abs xs; grind
  | _ => grind

open FullBeta in
/-- The inclusion `(· ⭢ₚ ·) ≤ (· ↠βᶠ ·)`. -/
lemma Parallel.le_reflTransGen_fullBeta :
    ((· ⭢ₚ ·) : Term Var → Term Var → Prop) ≤ (· ↠βᶠ ·) := by
  intro M N para
  induction para
  case fvar => exact .refl
  case app L L' R R' l_para m_para redex_l redex_m =>
    have : L.app R ↠βᶠ L'.app R := by grind
    grind [ReflTransGen.trans]
  case abs t t' xs _ ih =>
    apply redex_abs_cong xs
    grind
  case beta m m' n n' xs para_ih para_n redex_ih redex_n =>
    have m'_abs_lc : LC m'.abs := by
      apply LC.abs xs
      grind
    calc
      m.abs.app n ↠βᶠ
      m'.abs.app n :=
        redex_app_l_cong (redex_abs_cong xs (fun _ mem ↦ redex_ih _ mem)) (para_lc_l para_n)
      _           ↠βᶠ m'.abs.app n' := by grind
      _           ⭢βᶠ m' ^ n'       := by grind

/-- Multiple parallel reduction is equal to multiple β-reduction. -/
theorem reflTransGen_parallel_fullBeta :
    ((· ↠ₚ ·) : Term Var → Term Var → Prop) = (· ↠βᶠ ·) := by
  apply le_antisymm
  · exact reflTransGen_le_of_le Parallel.le_reflTransGen_fullBeta
  · exact ReflTransGen.mono FullBeta.le_parallel

/-- Parallel reduction respects substitution. -/
@[scoped grind .]
lemma para_subst (x : Var) (pm : M ⭢ₚ M') (pn : N ⭢ₚ N') : M[x := N] ⭢ₚ M'[x := N'] := by
  induction pm with
  | beta =>
    rw [subst_open _ _ _ _ (by grind)]
    refine Parallel.beta (free_union Var) ?_ ?_ <;> grind
  | app => constructor <;> assumption
  | abs => grind [Parallel.abs (free_union Var)]
  | _ => grind

/-- Parallel substitution respects closing and opening. -/
lemma para_open_close (x y z) (para : M ⭢ₚ M') : M⟦z ↜ x⟧⟦z ↝ fvar y⟧ ⭢ₚ M'⟦z ↜ x⟧⟦z ↝ fvar y⟧ :=
  by grind

/-- Parallel substitution respects fresh opening. -/
lemma para_open_out (L : Finset Var) (mem : ∀ x, x ∉ L → (M ^ fvar x) ⭢ₚ N ^ fvar x)
    (para : M' ⭢ₚ N') : (M ^ M') ⭢ₚ (N ^ N') := by
  grind [fresh_exists <| free_union [fv] Var]

/-! ### Complete developments and the triangle property

Following Takahashi, a parallel step `M ⭢ₚ N` can always be completed to the *complete development*
`M*` of `M`, which contracts all redexes of `M` at once: `N ⭢ₚ M*` (`para_dev_triangle`). The
diamond property of `⭢ₚ` follows immediately (`Diamond.of_triangle`).

The usual recursive definition of `M*` (with `(λ m) n ↦ m* ^ n*`) does not commute with opening on
locally nameless terms with dangling indices, so complete developments are defined here as a
relation, with cofinite quantification as for `Parallel`.
-/

/-- `Dev M M'` holds when `M'` is the complete development of `M`, which contracts all redexes of
`M` simultaneously. -/
inductive Dev : Term Var → Term Var → Prop
/-- Free variables develop to themselves. -/
| fvar (x : Var) : Dev (fvar x) (fvar x)
/-- An application that is not a redex develops both of its sides. -/
| app : ¬IsAbs t → Dev t t' → Dev u u' → Dev (app t u) (app t' u')
/-- An abstraction develops its body. -/
| abs (xs : Finset Var) :
    (∀ x ∉ xs, Dev (m ^ fvar x) (m' ^ fvar x)) → Dev (abs m) (abs m')
/-- A redex is contracted after developing both of its sides. -/
| beta (xs : Finset Var) :
    (∀ x ∉ xs, Dev (m ^ fvar x) (m' ^ fvar x)) → Dev n n' → Dev (app (abs m) n) (m' ^ n')

omit [HasFresh Var] [DecidableEq Var] in
/-- A complete development is a parallel reduction. -/
lemma Dev.to_parallel (h : Dev M N) : M ⭢ₚ N := by
  induction h <;> constructor <;> assumption

omit [HasFresh Var] in
/-- Renaming a free variable does not create an abstraction. -/
private lemma not_isAbs_subst_fvar {t : Term Var} (x y : Var) (h : ¬IsAbs t) :
    ¬IsAbs (t[x := fvar y]) := by
  cases t <;> grind

/-- Complete developments are preserved by renaming free variables. -/
lemma Dev.subst_fvar (x y : Var) (h : Dev M N) :
    Dev (M[x := Term.fvar y]) (N[x := Term.fvar y]) := by
  induction h with
  | fvar z => rw [Term.subst_fvar]; split <;> exact Dev.fvar _
  | app hna _ _ ih₁ ih₂ =>
    rw [subst_app, subst_app]
    exact Dev.app (not_isAbs_subst_fvar x y hna) ih₁ ih₂
  | abs xs _ ih =>
    rw [subst_abs, subst_abs]
    refine Dev.abs (xs ∪ {x}) fun z hz => ?_
    have hzx : x ≠ z := by grind
    rw [← subst_open_var z x _ _ hzx (LC.fvar y), ← subst_open_var z x _ _ hzx (LC.fvar y)]
    exact ih z (by grind)
  | beta xs _ _ ih₁ ih₂ =>
    rw [subst_app, subst_abs, subst_open x (Term.fvar y) _ _ (LC.fvar y)]
    refine Dev.beta (xs ∪ {x}) (fun z hz => ?_) ih₂
    have hzx : x ≠ z := by grind
    rw [← subst_open_var z x _ _ hzx (LC.fvar y), ← subst_open_var z x _ _ hzx (LC.fvar y)]
    exact ih₁ z (by grind)

/-- Every locally closed term has a complete development. -/
lemma Dev.exists_of_lc (h : LC M) : ∃ N, Dev M N := by
  induction h with
  | fvar x => exact ⟨_, Dev.fvar x⟩
  | abs L e _ ih =>
    -- Develop the body at one fresh variable `y`, then rename `y` to any other fresh variable.
    obtain ⟨y, hy⟩ := fresh_exists (L ∪ e.fv)
    obtain ⟨N, hN⟩ := ih y (by grind)
    have hN_lc : LC N := para_lc_r hN.to_parallel
    refine ⟨Term.abs (N ^* y), Dev.abs (L ∪ e.fv ∪ {y}) fun x hx => ?_⟩
    rw [subst_intro y (Term.fvar x) e (by grind),
      close_open_to_subst N (Term.fvar x) y hN_lc (LC.fvar x)]
    exact hN.subst_fvar y x
  | @app l r _ _ ih₁ ih₂ =>
    obtain ⟨l', hl'⟩ := ih₁
    obtain ⟨r', hr'⟩ := ih₂
    by_cases hl : IsAbs l
    · cases hl
      cases hl' with
      | abs xs hbody => exact ⟨_, Dev.beta xs hbody hr'⟩
    · exact ⟨_, Dev.app hl hl' hr'⟩

/-- **The triangle property** (Takahashi): a parallel step from `M` can be completed to the complete
development of `M` by another parallel step. -/
theorem para_dev_triangle (h : M ⭢ₚ N) : ∀ {D}, Dev M D → N ⭢ₚ D := by
  induction h with
  | fvar x =>
    intro D hD
    cases hD
    exact Parallel.fvar x
  | app hL hM ihL ihM =>
    intro D hD
    cases hD with
    | app _ hdL hdM => exact Parallel.app (ihL hdL) (ihM hdM)
    | beta xs hbody hdn =>
      -- The left side is an abstraction, so its parallel step is one as well.
      cases hL with
      | abs ys _ =>
        cases ihL (Dev.abs xs hbody) with
        | abs zs hz => exact Parallel.beta zs hz (ihM hdn)
  | abs xs _ ih =>
    intro D hD
    cases hD with
    | abs ys hdev => exact Parallel.abs (xs ∪ ys) fun x hx => ih x (by grind) (hdev x (by grind))
  | beta xs _ _ ihb ihn =>
    intro D hD
    cases hD with
    | app hna _ _ => exact absurd (IsAbs.abs _) hna
    | beta ys hdev hdn =>
      exact para_open_out (xs ∪ ys) (fun x hx => ihb x (by grind) (hdev x (by grind))) (ihn hdn)

/-- Parallel reduction has the diamond property. -/
theorem parallel_diamond : Diamond ((· ⭢ₚ ·) : Term Var → Term Var → Prop) := by
  refine Diamond.of_triangle fun M => ?_
  by_cases hM : LC M
  · obtain ⟨D, hD⟩ := Dev.exists_of_lc hM
    exact ⟨D, fun _ hN => para_dev_triangle hN hD⟩
  · exact ⟨M, fun _ hN => absurd (para_lc_l hN) hM⟩

/-- Parallel reduction is confluent. -/
theorem confluent_parallel : Confluent ((· ⭢ₚ ·) : Term Var → Term Var → Prop) :=
  parallel_diamond.to_confluent

/-- β-reduction is confluent. -/
@[wikidata Q1308502]
theorem confluent_fullBeta : Confluent ((· ⭢βᶠ ·) : Term Var → Term Var → Prop) := by
  change Diamond ((· ↠βᶠ ·) : Term Var → Term Var → Prop)
  rw [← reflTransGen_parallel_fullBeta]
  exact confluent_parallel

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
