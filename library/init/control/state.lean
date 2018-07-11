/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

The state monad transformer.
-/
prelude
import init.control.alternative init.control.lift
import init.control.id init.control.except
universes u v w

structure state_t (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
(run : σ → m (α × σ))

attribute [pp_using_anonymous_constructor] state_t

@[reducible] def state (σ α : Type u) : Type u := state_t σ id α

namespace state_t
section
  variables {σ : Type u} {m : Type u → Type v}

  variable  [monad m]
  variables {α β : Type u}

  @[inline] protected def pure (a : α) : state_t σ m α :=
  ⟨λ s, pure (a, s)⟩

  @[inline] protected def bind (x : state_t σ m α) (f : α → state_t σ m β) : state_t σ m β :=
  ⟨λ s, do (a, s') ← x.run s,
           (f a).run s'⟩

  instance : monad (state_t σ m) :=
  { pure := @state_t.pure _ _ _, bind := @state_t.bind _ _ _ }

  protected def orelse [alternative m] {α : Type u} (x₁ x₂ : state_t σ m α) : state_t σ m α :=
  ⟨λ s, x₁.run s <|> x₂.run s⟩

  protected def failure [alternative m] {α : Type u} : state_t σ m α :=
  ⟨λ s, failure⟩

  instance [alternative m] : alternative (state_t σ m) :=
  { failure := @state_t.failure _ _ _ _,
    orelse  := @state_t.orelse _ _ _ _ }

  @[inline] protected def get : state_t σ m σ :=
  ⟨λ s, pure (s, s)⟩

  @[inline] protected def put : σ → state_t σ m punit :=
  λ s', ⟨λ s, pure (punit.star, s')⟩

  @[inline] protected def modify (f : σ → σ) : state_t σ m punit :=
  ⟨λ s, pure (punit.star, f s)⟩

  @[inline] protected def lift {α : Type u} (t : m α) : state_t σ m α :=
  ⟨λ s, do a ← t, pure (a, s)⟩

  instance : has_monad_lift m (state_t σ m) :=
  ⟨@state_t.lift σ m _⟩

  @[inline] protected def monad_map {σ m m'} [monad m] [monad m'] {α} (f : Π {α}, m α → m' α) :
    state_t σ m α → state_t σ m' α :=
  λ x, ⟨λ st, f (x.run st)⟩

  instance (σ m m') [monad m] [monad m'] : monad_functor m m' (state_t σ m) (state_t σ m') :=
  ⟨@state_t.monad_map σ m m' _ _⟩

  def comm_except_t {ε m α} [monad m] (x : state_t σ (except_t ε m) α) : except_t ε (state_t σ m) α :=
  ⟨⟨λ st, do e ← (x.run st).run,
      pure $ match e with
      | except.ok (a, st') := (except.ok a, st')
      | except.error e     := (except.error e, st)⟩⟩

  instance {ε} : comm_monad_t (state_t σ) (except_t ε) :=
  ⟨@comm_except_t _ _⟩

  @[inline] protected def adapt {σ σ' σ'' α : Type u} {m : Type u → Type v} [monad m] (split : σ → σ' × σ'')
    (join : σ' → σ'' → σ) (x : state_t σ' m α) : state_t σ m α :=
  ⟨λ st, do let (st, ctx) := split st,
            (a, st') ← x.run st,
            pure (a, join st' ctx)⟩

  instance (ε) [monad_except ε m] : monad_except ε (state_t σ m) :=
  { throw := λ α, state_t.lift ∘ throw,
    catch := λ α x c, ⟨λ s, catch (x.run s) (λ e, state_t.run (c e) s)⟩ }
end
end state_t

/-- An implementation of [MonadState](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Class.html).
    In contrast to the Haskell implementation, we use overlapping instances to derive instances
    automatically from `monad_lift`. -/
class monad_state (σ : out_param (Type u)) (m : Type u → Type v) :=
/- Obtain the top-most state of a monad stack. -/
(get {} : m σ)
/- Set the top-most state of a monad stack. -/
(put {} : σ → m punit)
/- Map the top-most state of a monad stack.

   Note: `modify f` may be preferable to `f <$> get >>= put` because the latter
   does not use the state linearly (without sufficient inlining). -/
(modify {} : (σ → σ) → m punit)

export monad_state (get put modify)

section
variables {σ : Type u} {m : Type u → Type v}

-- NOTE: The ordering of the following two instances determines that the top-most `state_t` monad layer
-- will be picked first
instance monad_state_trans {n : Type u → Type w} [has_monad_lift m n] [monad_state σ m] : monad_state σ n :=
{ get := monad_lift (monad_state.get : m _),
  put := λ st, monad_lift (monad_state.put st : m _),
  modify := λ f, monad_lift (monad_state.modify f : m _) }

instance [monad m] : monad_state σ (state_t σ m) :=
{ get := state_t.get,
  put := state_t.put,
  modify := state_t.modify }
end

/-- Adapt a monad stack, changing the type of its top-most state.

    This class is comparable to [Control.Lens.Zoom](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Zoom), but does not use lenses (yet?), and is derived automatically for any transformer implementing `monad_functor`.

    For zooming into a part of the state, the `split` function should split σ into the part σ' and the "context" σ'' so that the potentially modified σ' and the context can be rejoined by `join` in the end.
    In the simplest case, the context can be chosen as the full outer state (ie. `σ'' = σ`), which makes `split` and `join` simpler to define. However, note that the state will not be used linearly in this case.

    Example:
    ```
    def zoom_fst {α σ σ' : Type} : state σ α → state (σ × σ') α :=
    adapt_state id prod.mk
    ```

    The function can also zoom out into a "larger" state, where the new parts are supplied by `split` and discarded by `join` in the end. The state is therefore not used linearly anymore but merely affinely, which is not a practically relevant distinction in Lean.

    Example:
    ```
    def with_snd {α σ σ' : Type} (snd : σ') : state (σ × σ') α → state σ α :=
    adapt_state (λ st, ((st, snd), ())) (λ ⟨st,snd⟩ _, st)
    ```

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_state_functor (σ σ' : out_param (Type u)) (n n' : Type u → Type u) :=
    (map {} {α : Type u} : (∀ {m : Type u → Type u} [monad m], state_t σ m α → state_t σ' m α) → n α → n' α)
    ```
    which better describes the intent of "we can map a `state_t` anywhere in the monad stack".
    If we look at the unfolded type of the first argument `∀ m [monad m], (σ → m (α × σ)) → σ' → m (α × σ')`, we see that it has the lens type `∀ f [functor f], (α → f α) → β → f β` with `f` specialized to `λ σ, m (α × σ)` (exercise: show that this is a lawful functor). We can build all lenses we are insterested in from the functions `split` and `join` as
    ```
    λ f _ st, let (st, ctx) := split st in
              (λ st', join st' ctx) <$> f st
    ```
    -/
class monad_state_adapter (σ σ' : out_param (Type u)) (m m' : Type u → Type v) :=
(adapt_state {} {σ'' α : Type u} (split : σ' → σ × σ'') (join : σ → σ'' → σ') : m α → m' α)
export monad_state_adapter (adapt_state)

section
variables {σ σ' : Type u} {m m' : Type u → Type v}

def monad_state_adapter.adapt_state' [monad_state_adapter σ σ' m m'] {α : Type u} (to_σ : σ' → σ) (from_σ : σ → σ') : m α → m' α :=
adapt_state (λ st, (to_σ st, punit.star)) (λ st _, from_σ st)
export monad_state_adapter (adapt_state')

instance monad_state_adapter_trans {n n' : Type u → Type v} [monad_functor m m' n n'] [monad_state_adapter σ σ' m m'] : monad_state_adapter σ σ' n n' :=
⟨λ σ'' α split join, monad_map (λ α, (adapt_state split join : m α → m' α))⟩

instance [monad m] : monad_state_adapter σ σ' (state_t σ m) (state_t σ' m) :=
⟨λ σ'' α, state_t.adapt⟩
end

instance (σ : Type u) (m out : Type u → Type v) [functor m] [monad_run out m] : monad_run (λ α, σ → out α) (state_t σ m) :=
⟨λ α x, run ∘ (λ σ, prod.fst <$> (x.run σ))⟩

class monad_state_runner (σ : Type u) (m m' : Type u → Type u) :=
(run_state {} {α : Type u} : m α → σ → m' α)
export monad_state_runner (run_state)

section
variables {σ σ' : Type u} {m m' : Type u → Type u}

instance monad_state_runner_trans {n n' : Type u → Type u} [monad_functor m m' n n'] [monad_state_runner σ m m'] : monad_state_runner σ n n' :=
⟨λ α x s, monad_map (λ α (y : m α), (run_state y s : m' α)) x⟩

instance state_t.monad_state_runner [monad m] : monad_state_runner σ (state_t σ m) m :=
⟨λ α x s, prod.fst <$> x.run s⟩
end
