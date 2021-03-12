/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Meta

namespace Std
-- We put `Range` in `Init` because we want the notation `[i:j]`  without importing `Std`
-- We don't put `Range` in the top-level namespace to avoid collisions with user defined types
structure Range where
  start : Nat := 0
  stop  : Nat
  step  : Nat := 1
  ascending : Bool := true

namespace Range
universes u v

/-- Raw size of the range (i.e., `stop - start`). -/
@[inline] def size (range : Range) : Nat :=
  range.stop - range.start

/-- Number of `Nat`s the range will include in an iteration. -/
@[inline] def steps (range : Range) : Nat :=
  let size := range.size
  let step := range.step
  size / step + (if size % step = 0 then 0 else 1)

/-- A range with the same size and steps but in reverse order. -/
@[inline] def reverse (range : Range) : Range :=
  {range with ascending := !range.ascending}

/-- Initial value for an iteration over this range. -/
@[inline] def initial (range : Range) : Nat :=
  if range.ascending
  then range.start
  else range.start + (range.step * (range.steps - 1))

/-- The value one step after `cur` in `range`. N.B., this function assumes
  `cur` is a valid value in `range` and that there is a logically valid
  additional step to take (i.e., that `cur` isn't already the last value
  in `range`). -/
@[inline] def next! (range : Range) (cur : Nat) : Nat :=
  if range.ascending
  then cur + range.step
  else cur - range.step

@[inline] def forIn {β : Type u} {m : Type u → Type v} [Monad m] (range : Range) (init : β) (f : Nat → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (fuel : Nat) (index : Nat) (b : β) : m β := do
    match fuel with
    | 0   => pure b
    | n+1 => match ← f index b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop n (range.next! index) b
  loop range.steps range.initial init

instance : ForIn m Range Nat where
  forIn := Range.forIn

@[inline] protected def forM {m : Type u → Type v} [Monad m] (range : Range) (f : Nat → m PUnit) : m PUnit :=
  let rec @[specialize] loop (fuel : Nat) (index : Nat) : m PUnit := do
    match fuel with
    | 0   => pure ⟨⟩
    | fuel+1 => f index; loop fuel (range.next! index)
  loop range.steps range.initial

instance : ForM m Range Nat where
  forM := Range.forM

syntax:max "[" ":" term "]" : term
syntax:max "[" term ":" term "]" : term
syntax:max "[" ":" term ":" term "]" : term
syntax:max "[" term ":" term ":" term "]" : term

macro_rules
  | `([ : $stop]) => `({ stop := $stop : Range })
  | `([ $start : $stop ]) => `({ start := $start, stop := $stop : Range })
  | `([ $start : $stop : $step ]) => `({ start := $start, stop := $stop, step := $step : Range })
  | `([ : $stop : $step ]) => `({ stop := $stop, step := $step : Range })

end Range
end Std
