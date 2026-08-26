/-
Copyright (c) 2026 The Strong-Coupling Lattice Yang--Mills Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Strong-Coupling Lattice Yang--Mills contributors
-/

import Mathlib

/-!
# Extracting a one-link power lower bound

Once locality identifies a nonzero leading Taylor coefficient, analytic
factorization writes the one-link correlation as `beta ^ r * h beta` with a
positive continuous leading factor. This file proves the final real-variable
step needed in Milestone 3.
-/

namespace YangMills.Gluelump.OneLink

open Metric Filter Set
open scoped Topology

/-- A positive continuous leading factor supplies a uniform positive power
lower bound to its product with `beta ^ r` on a punctured right neighborhood
of the origin. -/
theorem power_lower_bound_of_continuous_factor (r : ℕ) {h : ℝ → ℝ}
    (hh : ContinuousAt h 0) (hh0 : 0 < h 0) :
    ∃ c0 > 0, ∃ beta0 > 0, ∀ beta, 0 < beta → beta ≤ beta0 →
      c0 * beta ^ r ≤ beta ^ r * h beta := by
  let c0 := h 0 / 2
  have hc0 : 0 < c0 := half_pos hh0
  have hc0lt : c0 < h 0 := by dsimp [c0]; linarith
  have hneighborhood : {x : ℝ | c0 < h x} ∈ 𝓝 0 :=
    hh.tendsto (Ioi_mem_nhds hc0lt)
  obtain ⟨epsilon, hepsilon, hepsilon_sub⟩ :=
    Metric.mem_nhds_iff.mp hneighborhood
  let beta0 := epsilon / 2
  have hbeta0 : 0 < beta0 := half_pos hepsilon
  refine ⟨c0, hc0, beta0, hbeta0, ?_⟩
  intro beta hbeta hbeta_le
  have hdist : dist beta 0 < epsilon := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hbeta]
    exact hbeta_le.trans_lt (half_lt_self hepsilon)
  have hfactor : c0 < h beta := hepsilon_sub hdist
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left hfactor.le (pow_nonneg hbeta.le r)

/-- Version for a function already identified with its leading-power
factorization on a right neighborhood. -/
theorem power_lower_bound_of_eventual_factorization (r : ℕ)
    {f h : ℝ → ℝ} (hh : ContinuousAt h 0) (hh0 : 0 < h 0)
    (hfactor : ∀ᶠ beta in 𝓝[>] 0, f beta = beta ^ r * h beta) :
    ∃ c0 > 0, ∃ beta0 > 0, ∀ beta, 0 < beta → beta ≤ beta0 →
      c0 * beta ^ r ≤ f beta := by
  obtain ⟨c0, hc0, beta0, hbeta0, hlower⟩ :=
    power_lower_bound_of_continuous_factor r hh hh0
  rw [eventually_nhdsWithin_iff] at hfactor
  obtain ⟨s, hs, hsopen, h0s⟩ := _root_.mem_nhds_iff.mp hfactor
  obtain ⟨delta, hdelta, hdelta_sub⟩ := Metric.isOpen_iff.mp hsopen 0 h0s
  let beta1 := min beta0 (delta / 2)
  have hbeta1 : 0 < beta1 := lt_min hbeta0 (half_pos hdelta)
  refine ⟨c0, hc0, beta1, hbeta1, ?_⟩
  intro beta hbeta hbeta_le
  have hbeta_beta0 : beta ≤ beta0 := hbeta_le.trans (min_le_left _ _)
  have hdist : dist beta 0 < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hbeta]
    exact (hbeta_le.trans (min_le_right _ _)).trans_lt (half_lt_self hdelta)
  have hbeta_s : beta ∈ s := hdelta_sub hdist
  rw [hs hbeta_s (by simpa using hbeta)]
  exact hlower beta hbeta hbeta_beta0

end YangMills.Gluelump.OneLink
