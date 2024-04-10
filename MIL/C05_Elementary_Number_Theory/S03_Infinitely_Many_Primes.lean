import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Order
import MIL.Common

open BigOperators

namespace C05S03

/-- 0でも1でもない自然数は2以上 -/
theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat' apply Nat.succ_le_succ
    apply zero_le

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

/-- 2以上の自然数には，素因数が存在する -/
theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  . rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

/-- 素数は無限に存在する．
つまり，任意の自然数 `n` に対して `n` よりも大きい素数が存在する. -/
theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
    suffices 1 ≤ Nat.factorial (n + 1) from Nat.le_add_of_sub_le this
    have := Nat.monotone_factorial (show 0 ≤ n + 1 from by simp_arith)
    nth_rw 1 [show 1 = Nat.factorial 0 from rfl]
    assumption
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine' ⟨p, _, pp⟩
  show p > n
  by_contra ple
  push_neg  at ple
  have : p ∣ Nat.factorial (n + 1) := by
    apply Nat.dvd_factorial pp.pos (by linarith)
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp
  show False
  aesop
open Finset

section
-- `α` は集合で，
-- `r`, `s`, `t` は `α` の有限部分集合だとする
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  aesop

example : (r \ s) \ t = r \ (s ∪ t) := by
  aesop

end

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i in s, i :=
  Finset.dvd_prod_of_mem _ h

/-- `p, q` がともに素数で整除関係があるならば，`p = q`.-/
theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  obtain ⟨k, hk⟩ := h
  have := prime_q.isUnit_or_isUnit' p k (by assumption)
  simp at this
  have pn : p ≠ 1 := by apply prime_p.ne_one
  simp_all

/-- 素数だけからなる有限集合 `s` があって，`p` が `∏ n in s` を割り切るならば，
`p` は `s` の要素 -/
theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n in s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]

  have primea := h₀.left
  rcases h₁ with h | h

  case inl =>
    obtain ⟨k, hk⟩ := h
    left
    have irr := primea.isUnit_or_isUnit' p k (by assumption)
    replace irr : k = 1 := by
      clear * - irr prime_p
      aesop
    simp [irr] at hk
    simp_all

  case inr =>
    have allprime := h₀.right
    specialize ih allprime h
    right
    assumption

example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter

/-- 任意の有限集合 `s` に対して，`s` に含まれない素数 `p` が存在する. -/
theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  -- 有限集合 `s` が与えられたとする
  intro s

  -- 背理法で示す．そのような素数 `p` が存在しないと仮定する
  by_contra! h

  -- `s` の要素のうち素数であるものだけを集めて，`s'` とする.
  set s' := s.filter Nat.Prime with s'_def

  -- `s` はすべての素数を含むと仮定したので，
  -- `n ∈ s'` と `n` が素数であることは同値．
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h

  -- ここで `s'` の要素の積に1を足したものは2以上であり，
  have : 2 ≤ (∏ i in s', i) + 1 := by
    suffices 1 ≤ ∏ i in s', i from by linarith
    suffices ∀ n ∈ s', 1 ≤ n from by exact one_le_prod' this
    intro n hn
    have := mem_s'.mp hn
    replace := Nat.Prime.two_le this
    linarith

  -- したがって，`(∏ i in s', i) + 1` の素因数 `p` が存在する
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩

  -- 一方で，`p` は素数なので，`p ∈ s'` である
  have pmem : p ∈ s' := by
    rwa [mem_s']

  -- ゆえに `p` は `s'` の要素の総積を割り切る
  have : p ∣ ∏ i in s', i := by
    exact dvd_prod_of_mem (fun i ↦ i) pmem

  -- このことから，`p` は `1` を割り切らなければならない
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp

  -- これは矛盾である
  show False
  aesop

/-- `Q` を `ℕ` 上の述語であるとする．このとき `{k // Q k} ⊆ s` なる
有限集合 `s` が存在するならば，`{k // Q k}` は有界である．-/
theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

/-- `Q` を `ℕ` 上の述語であるとする．このとき `{k // Q k}` が有界ならば，
`{k // Q k} = s` なる有限集合 `s` が存在する. -/
theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k

example : 27 % 4 = 3 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]
  norm_num

/-- `m * n` を4で割った余りが3なら，`m` か `n` のどちらかは
4で割った余りが3になる -/
theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases hm : m % 4 <;> simp [hm]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases hn : n % 4 <;> simp [hn] ; decide

/-- `n` を4で割った余りが3なら，`n` は2以上 -/
theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h

/-- `m` が `n` の自明でない約数ならば `k := n / m` も `n` の自明でない約数になる -/
theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  -- `k := n / m` とおく
  set k := n / m with hk

  -- このとき `m * k = n` が成り立つ
  replace hk : m * k = n := by
    rw [hk]
    exact Nat.mul_div_cancel' h₀

  constructor

  -- まず `k ∣ n` だが，これは明らか．
  case left =>
    use m
    linarith

  -- 次に `k < n` を示す．
  case right =>
    -- 背理法で示す
    by_contra! h

    -- 仮定から `n ≥ 2 * n` が成り立つ
    have := calc
      n = m * k := by rw [hk]
      _ ≥ 2 * k := by gcongr
      _ ≥ 2 * n := by gcongr

    -- よって `n = 0` であり `m < 0`.
    replace : n = 0 := by linarith
    rw [this] at h₂

    -- これは矛盾である
    linarith

/-- 4で割って3余る自然数 `n` には，4で割って3余るような素因数 `p` が存在する -/
theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  -- `n` が素数かどうかで場合分けする
  by_cases np : n.Prime

  -- `n` が素数ならば示すべきことはない
  -- 以下，`n` は素数でないとしてよい．
  focus use n

  -- `n` に関する完全帰納法で証明する
  induction' n using Nat.strong_induction_on with n ih

  -- `n` は素数ではないので，自明でない約数 `m` が存在する
  rw [Nat.prime_def_lt] at np
  push_neg at np
  have nge2 : 2 ≤ n := two_le_of_mod_4_eq_3 h
  obtain ⟨m, mltn, mdvdn, mne1⟩ := np nge2

  -- 特に `m` は2以上.
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith

  -- `k := n / m` とおくと `n = m * k` であり，
  -- `m` か `k` のどちらかは4で割って3余る
  set k := n / m
  have neq : m * k = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ k % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]

  rcases this with h1 | h1

  focus
    -- `m` が4で割って3余る場合
    guard_hyp h1 : m % 4 = 3

    -- `m` が素数でないと仮定してよい
    by_cases mp : m.Prime
    case pos => exact ⟨m, mp, mdvdn, h1⟩; done
    focus

    -- 帰納法の仮定より，`m` には4で割って3余る素因数 `p` が存在する
    specialize ih m mltn h1 mp
    obtain ⟨p, ph, pdiv, pmod⟩ := ih

    -- この `p` が所望の素因数である
    use p
    suffices p ∣ n from by aesop
    clear * - pdiv mdvdn
    calc
      p ∣ m := pdiv
      _ ∣ n := by exact mdvdn

  focus
    -- `k` が4で割って3余る場合
    guard_hyp h1 : k % 4 = 3

    -- `k` は素数でないと仮定してよい
    by_cases kp : k.Prime
    case pos =>
      use k
      suffices k ∣ n from by aesop
      use m; clear * - neq
      linarith
    focus

    -- 帰納法の仮定より，`k` には4で割って3余る素因数 `p` が存在する
    specialize ih k (aux mdvdn mge2 mltn).right h1 kp
    obtain ⟨p, ph, pdiv, pmod⟩ := ih

    -- この `p` が所望の素因数である
    use p
    suffices p ∣ n from by aesop
    clear * - pdiv neq
    calc
      p ∣ k := pdiv
      _ ∣ n := by use m; linarith

  -- 証明終わり
  done

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption

theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i in erase s 3, i) + 3) % 4 = 3 := by
    sorry
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
    sorry
  have pne3 : p ≠ 3 := by
    sorry
  have : p ∣ 4 * ∏ i in erase s 3, i := by
    sorry
  have : p ∣ 3 := by
    sorry
  have : p = 3 := by
    sorry
  contradiction
