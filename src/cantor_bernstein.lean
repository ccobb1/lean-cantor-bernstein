import logic.function.basic
import tactic

noncomputable theory
open_locale classical

open set function classical


/-
The Cantor-Bernstein Theorem: For any sets `A, B`, if there exist injections
`f: A → B` and `g: B → A`, there exists a bijection `h: A → B`.
-/

variables {A B : Type}

/-
The proof of the theorem is based on the following informal reasoning: Look at
the directed bipartite graph with vertex sets `A` and `B` and edges defined by
`f` and `g`. Each connected component of this graph can be seen to fall into
one of four categories:

1) An infinite path starting at a vertex in `A`,
2) An infinite path starting at a vertex in `B`,
3) An infinite path extending in both directions,
4) A directed cycle.

In case 1, we can create a bijection on that component by mapping each vertex
`a ∈ A` to the next one in the path, `f(a)`.
In case 2, we can create a bijection by mapping each vertex `a ∈ A` to the
previous one in the path, `g⁻¹(a)`.
In case 3 and 4, we could go with either the scheme for case 1 or the scheme
for case 2 -- we'll arbitrarily go with the case 1 scheme.
Taken together, these define a bijection `A → B`.

In other words, we want to define a function `h : A → B` such that
`h(a) = g⁻¹(a)` whenever `a` belongs to a case 2 component, and `h(a) = f(a)`
otherwise, and then argue that `h` is a bijection.

In order to define `h`, we should first define a predicate that tells whether
`a` belongs to a case 2 component. We start by defining a relation `follows`,
which, given vertices `a ∈ A` and `b ∈ B`, says whether `a` follows `b`, i.e.,
there's a directed path in the graph from `b` to `a`. (In retrospect, my
terminology may be a bit counterintuitive, depending on how you look at it.)

We can define this inductively. Our base case is when `a` comes immediately
after `b`, i.e., when `g(b) = a`. Then, if `a` follows `b`, then `g(f(a))`
will follow `b` as well.
-/

inductive follows (f : A → B) (g : B → A) : A → B → Prop
| base {a : A} {b : B} : g b = a → follows a b
| step {a : A} {b : B} : follows a b → follows (g (f a)) b


/-
Now we can define the set of elements of `A` in case 2 components; we call them
the `B_led` elements. Namely, these are the elements `a ∈ A` that follow some
`b ∈ B` which "leads" a path, i.e., there's nothing that maps to `b`.
-/

def B_led (f : A → B) (g : B → A) : set A :=
{ a : A | ∃ b : B, (follows f g a b ∧ ∀ a : A, f a ≠ b) }


/-
There's one more step before we can properly define `h`: we have to check that
the inverse of `g` is well-defined on `B_led` elements. This is "obvious",
since if nothing mapped to `a ∈ A`, then it would be the leader in an `A_led`
component. However, we still have to prove it!
-/

lemma has_g_inv {f : A → B} {g : B → A} {a : A} (hyp_a : B_led f g a) :
∃ b, g b = a :=
begin
  cases hyp_a with p hyp_p,
  replace hyp_p := hyp_p.left,
  induction hyp_p with a b,
  use b, assumption, use f hyp_p_a,
end

/-
Now, we can define a function that, given a proof that `a` is `B_led`, returns
`g⁻¹(a)`. (Well, technically, we're just returning *some* inverse of `a` -- we
haven't proved that the inverse is unique. We could do so easily, but it turns
out we don't need to.)
-/

def g_inv {f : A → B} {g : B → A} {a : A} (hyp_a : B_led f g a) : B :=
  some (has_g_inv hyp_a)

/-
And a quick lemma: `g(g⁻¹(a)) = a` for any `B_led` element `a`.
-/

lemma inv_eq {f : A → B} {g : B → A} {a : A} (hyp : B_led f g a) :
g (g_inv hyp) = a := some_spec (has_g_inv hyp)


/-
We're finally ready to prove the bulk of the theorem. We'll actually prove a
stronger version, which we used in our proof of the countable Hall matching
theorem: there exists a bijection that, regarded as a graph, is a subgraph of
the graph defined by `f` and `g`. In other words, whenever `h(a) = b`, we have
either `f(a) = b` or `g(b) = a`. This doesn't add much extra work, since it's
fairly obvious from the definition of `h`.
-/

theorem cantor_bernstein_strong {f : A → B} {g : B → A} (hyp_f : injective f)
(hyp_g : injective g) :
∃ h : A → B, bijective h ∧ ∀ a b, h a = b → f a = b ∨ g b = a :=
begin
  /-
  Here we define h: if `a` is `B_led`, then `h(a) = g⁻¹(a)`, else `h(a) = f(a)`.
  -/
  let h := λ a, dite (B_led f g a) (λ hyp_a, g_inv hyp_a) (λ _, f a),
  use h,
  /-
  We prove injectivity, then surjectivity, then the added "strong" property.
  -/
  split, split,
  {
    /-
    The bulk of the proof of injectivity is showing that, if `h(a₁) = h(a₂)`,
    then `a₁` and `a₂` belong to the same connected component. Thus, they're
    either both `B_led` or both not, and in either case injectivity follows
    pretty much immediately.

    The proof can be informally stated as follows:

    Suppose for sake of contradiction that `h(a₁) = h(a₂)`, but `a₁` is `B_led`
    and `a₂` isn't. Then `g⁻¹(a₁) = f(a₂)`, so `a₁ = g(f(a₂))`.

    Intuitively, we can see that this means `a₁` comes 2 steps after `a₂` in a 
    path, so they're in the same connected component, a contradiction.
    
    Putting it formally requires us to go back to our inductive definition of
    "following". Let `b` be the leader of `a₁`'s component, so `a` follows `b`.
    
    The `base` case where `a₁` immediately follows `b` is impossible, since
    otherwise `a₂` would point to `b`, contradicting `b`'s status as leader.
    
    But this leaves us with the `step` case, which implies there's some `a`
    for which `a` follows `b` and `f(g(a)) = a₁ = f(g(a₂))`. Injectivity then
    implies `a = a₂`, so `a₂` follows `b`, and is thus `B_led` -- contradiction.
    -/
    have impossible_case : ∀ a₁ a₂ : A,
    h a₁ = h a₂ → B_led f g a₁ → ¬B_led f g a₂ → false :=
    begin
      intros a₁ a₂ hyp_a hyp_1 hyp_2,
      apply hyp_2,
      simp [h, dif_pos hyp_1, dif_neg hyp_2] at hyp_a,
      clear hyp_2 h,
      replace hyp_a := congr_arg g hyp_a, rw inv_eq hyp_1 at hyp_a,

      cases hyp_1 with b hyp_b,
      use b,
      cases hyp_b,
      rw and_iff_left hyp_b_right,
      cases hyp_b_left with _ _ hyp_base a _ hyp_step,
      {
        apply false.elim, apply hyp_b_right a₂,
        apply hyp_g,
        rw [← hyp_a, hyp_base],
      },
      {
        rwa ← hyp_f (hyp_g hyp_a),
      },
    end,
    /-
    This finishes the "impossible case" -- the rest of the injectivity proof is
    pretty straightforward.
    -/
    intros a₁ a₂ hyp_a,
    cases classical.em (B_led f g a₁) with hyp_1 hyp_1;
    cases classical.em (B_led f g a₂) with hyp_2 hyp_2,
    {
      simp [h, dif_pos hyp_1, dif_pos hyp_2] at hyp_a,
      rw [← inv_eq hyp_1, ← inv_eq hyp_2],
      exact congr_arg g hyp_a,
    },
    {
      exact false.elim (impossible_case a₁ a₂ hyp_a hyp_1 hyp_2),
    },
    {
      exact false.elim (impossible_case a₂ a₁ (hyp_a.symm) hyp_2 hyp_1),
    },
    {
      simp [h, dif_neg hyp_1, dif_neg hyp_2] at hyp_a,
      exact hyp_f hyp_a,
    },
  },
  {
    /-
    The proof of surjectivity is roughly as follows:

    Take an arbitrary `b ∈ B`, and do casework on whether `g(b)` is `B_led`.

    If `g(b)` is `B_led`, then `h(g(b)) = g⁻¹(g(b)) = b`, so `g(b)` works and
    we're done.

    Otherwise, `g(b)` isn't `B_led`. This implies that there exists `a` such
    that `f(a) = b` -- otherwise, `b` would be a leader of `g(b)`'s component.

    Note that `a` can't be `B_led`, since otherwise `g(b) = g(f(a))` would also
    be `B_led` (as immediately implied by the `step` case).

    Thus, `h(a) = f(a) = b`, so `a` works and we're done.
    -/
    intro b,
    cases classical.em (B_led f g (g b)) with hyp_1 hyp_1,
    {
      use g b,
      simp [h, dif_pos hyp_1],
      apply hyp_g, apply inv_eq,
    },
    {
      have has_f_inv : ∃ a, f a = b :=
      begin
        rw [B_led, ← @mem_def _ _ {a | _}, nmem_set_of_eq] at hyp_1,
        simp at hyp_1,
        specialize hyp_1 b,
        apply hyp_1,
        exact follows.base rfl,
      end,
      cases has_f_inv with a hyp_2,
      use a,
      rw ← hyp_2 at hyp_1,
      replace hyp_1 : ¬B_led f g a :=
      begin
        revert hyp_1, rw not_imp_not, intros hyp,
        cases hyp with b hyp_b,
        use b,
        exact ⟨(follows.step hyp_b.left), hyp_b.right⟩,
      end,
      simpa [h, dif_neg hyp_1],
    },
  },
  {
    /-
    All that's left is to prove the extra fact about `h`, but this is very
    straightforward.
    -/
    intros a b hyp,
    simp [h] at hyp,
    cases classical.em (B_led f g a) with hyp_pos hyp_neg,
    {
      replace hyp := congr_arg g hyp,
      rw [dif_pos hyp_pos, inv_eq hyp_pos] at hyp,
      exact or.intro_right _ hyp.symm,
    },
    {
      rw dif_neg hyp_neg at hyp,
      exact or.intro_left _ hyp,
    },
  },
end


/-
We've now formally proved the Cantor-Bernstein theorem -- yay!

Here's the "normal" version, which obviously follows from the "strong" version.
-/

theorem cantor_bernstein {f : A → B} {g : B → A} (hyp_f : injective f)
(hyp_g : injective g) : ∃ h : A → B, bijective h :=
begin
  have cbs := cantor_bernstein_strong hyp_f hyp_g,
  cases cbs with h hyp_h,
  exact Exists.intro h hyp_h.left,
end