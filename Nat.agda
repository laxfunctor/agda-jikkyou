module Nat where
  {-
  Curry-Howard
  f : A → B
  a : A
  ----------
  f a : B
  -}

  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  one = suc zero
  two = suc one

  data _==_ (n : ℕ) : ℕ → Set where
    refl : n == n

  ==trans : ∀ {l m n : ℕ} → l == m → m == n → l == n
  ==trans {l} {.l} {.l} refl refl = refl

  ==sym : ∀ {m n : ℕ} → m == n → n == m
  ==sym {m} {.m} refl = refl

  suc= : ∀ {m n : ℕ} → m == n → (suc m) == (suc n)
  suc= {m} {.m} refl = refl

  add : ℕ → ℕ → ℕ
  add zero m = m
  add (suc n) m = suc (add n m)

  _+_ = add

  1+1=2 : (one + one) == two
  1+1=2 = refl

  n+0=n : ∀ {n : ℕ} → (n + zero) == n
  n+0=n {zero} = refl
  n+0=n {suc n} = suc= n+0=n

  n=n+0 : ∀ {n : ℕ} → n == (n + zero)
  n=n+0 {n} = ==sym n+0=n

  suc[m+n]=m+suc[n] : ∀ {m n : ℕ} → (suc (m + n)) == (m + (suc n))
  suc[m+n]=m+suc[n] {zero} {n} = refl
  suc[m+n]=m+suc[n] {suc m} {n} = suc= suc[m+n]=m+suc[n]

  m+suc[n]=suc[m+n] : ∀ {m n : ℕ} → (m + (suc n)) == (suc (m + n))
  m+suc[n]=suc[m+n] = ==sym suc[m+n]=m+suc[n]

  commutativity+ : ∀ {m n : ℕ} → (m + n) == (n + m)
  commutativity+ {zero} {n} = n=n+0
  commutativity+ {suc m} {zero} = suc= n+0=n
  commutativity+ {suc m} {suc n} =
    suc= (==trans m+suc[n]=suc[m+n]
      (==trans (suc= (commutativity+ {m} {n})) suc[m+n]=m+suc[n]))


