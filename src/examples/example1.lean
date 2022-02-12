/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import tactic

/-! # Lean lab 1

## Summary

We practice tactics for doing high school algebra problems:
* `linear_combination`
* `ring`
* `rwa`
and a couple of more general tactics,
* `have` 
* `calc`
-/


/-! Example 1 -/

example {x : ℤ} (hx : x + 4 = 2) : x = -2 :=
begin
  linear_combination hx,
end

/-! Example 2 -/

example {x : ℝ} (hx : x + 4 = 2) : x = -2 :=
begin
  linear_combination hx,
end

example {x : ℝ} (hx : x + 4 = 2) : x = -2 :=
begin
  calc x = (x + 4) - 4 : by ring
  ... = 2 - 4 : by rwa [hx]
  ... = -2 : by ring,
end

/-! Example 3 -/

example {x y : ℚ} (h : x = 2 * y + 1) : 3 * x - 1 = 2 * (3 * y + 1) :=
begin
  calc 3 * x - 1 = 3 * (2 * y + 1) - 1 : by rwa [h]
  ... = 2 * (3 * y + 1) :  by ring,
end

example {x y : ℚ} (h : x = 2 * y + 1) : 3 * x - 1 = 2 * (3 * y + 1) :=
begin
  linear_combination (h, 3),
end

/-! Example 4 -/

example {p : ℝ} (hp : 3 * p + 1 = 5 * p - 3) : p = 2 :=
begin
  have h1 : 4 = 2 * p := by linear_combination hp,
  symmetry,
  linear_combination (h1, 1/2),
end

example {p : ℝ} (hp : 3 * p + 1 = 5 * p - 3) : p = 2 :=
begin
  have h : 2 * p = 4,
  { calc 2 * p = (5 * p - 3) - 3 * p + 3 : by ring
    ... = (3 * p + 1) - 3 * p + 3 : by rwa [← hp]
    ... = 4 : by ring },
  linear_combination (h, 1/2),
end

example {p : ℝ} (hp : 3 * p + 1 = 5 * p - 3) : p = 2 :=
begin
  linear_combination (hp, -1/2),
end