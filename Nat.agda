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

  infix 10 _==_

  ==trans : ∀ {l m n : ℕ} → l == m → m == n → l == n
  ==trans {l} {.l} {.l} refl refl = refl

  ==sym : ∀ {m n : ℕ} → m == n → n == m
  ==sym {m} {.m} refl = refl

  proof== : (n : ℕ) → n == n
  proof== n = refl
  _===_by[_] : {l m : ℕ} → (l == m) → (n : ℕ) → (m == n) → (l == n)
  _===_by[_] {l} {m} q n p = ==trans q p
  infixl 10 _===_by[_]

  suc= : ∀ {m n : ℕ} → m == n → (suc m) == (suc n)
  suc= {m} {.m} refl = refl

  add : ℕ → ℕ → ℕ
  add zero m = m
  add (suc n) m = suc (add n m)

  _+_ = add
  infixl 30 _+_

  1+1=2 : (one + one) == two
  1+1=2 = refl

  n+0=n : ∀ {n : ℕ} → (n + zero) == n
  n+0=n {zero} = refl
  n+0=n {suc n} = suc= n+0=n

  n=n+0 : ∀ {n : ℕ} → n == (n + zero)
  n=n+0 {n} = ==sym n+0=n

  suc[m+n]=m+suc[n] : ∀ {m n : ℕ} → suc (m + n) == m + (suc n)
  suc[m+n]=m+suc[n] {zero} {n} = refl
  suc[m+n]=m+suc[n] {suc m} {n} = suc= suc[m+n]=m+suc[n]

  m+suc[n]=suc[m+n] : ∀ {m n : ℕ} → m + (suc n) == suc (m + n)
  m+suc[n]=suc[m+n] = ==sym suc[m+n]=m+suc[n]

  commutativity+ : ∀ {m n : ℕ} → (m + n) == (n + m)
  commutativity+ {zero} {n} = n=n+0
  commutativity+ {suc m} {zero} = suc= n+0=n
  commutativity+ {suc m} {suc n} =
    suc= (==trans m+suc[n]=suc[m+n]
      (==trans (suc= (commutativity+ {m} {n})) suc[m+n]=m+suc[n]))

  associativity+ : ∀ {l m n : ℕ} → (l + m) + n == l + (m + n)
  associativity+ {zero} {m} {n} = refl
  associativity+ {suc l} {m} {n} = suc= (associativity+ {l} {m})

  mult : ℕ → ℕ → ℕ
  mult zero n = zero
  mult (suc m) n = n + mult m n
  _*_ = mult
  infixl 40 _*_

  0=n*0 : ∀ {n : ℕ} → zero == n * zero
  0=n*0 {zero} = refl
  0=n*0 {suc n} = 0=n*0 {n}

  n*0=0 : ∀ {n : ℕ} → n * zero == zero
  n*0=0 {n} = ==sym (0=n*0 {n})

  add= : ∀ {l m n : ℕ} → m == n → l + m == l + n
  add= {l} {m} {.m} refl = refl

  =add : ∀ {l m n : ℕ} → m == n → m + l == n + l
  =add {l} {m} {.m} refl = refl

  commutativity* : ∀ {m n : ℕ} → m * n == n * m
  commutativity* {zero} {n} =
    proof==
      (zero * n)
      === zero by[ refl ]
      === n * zero by[ 0=n*0 {n} ]
  commutativity* {suc m} {zero} =
    proof==
      (suc m * zero)
      === zero + m * zero by[ refl ]
      === m * zero by[ refl ]
      === zero by[ n*0=0 {m} ]
      === zero * suc m by[ refl ]
  commutativity* {suc m} {suc n} =
    proof==
      (suc m * suc n)
      === suc n + m * suc n by[ refl ]
      === suc (n + m * suc n) by[ refl ]
      === suc (n + suc n * m) by[ suc= (add= (commutativity* {m})) ]
      === suc (n + (m + n * m)) by[ refl ]
      === suc ((n + m) + (n * m)) by[ suc= (==sym (associativity+ {n} {m} {n * m})) ]
      === suc ((m + n) + (n * m)) by[ suc= (=add (commutativity+ {n})) ]
      === suc ((m + n) + (m * n)) by[ suc= (add= (commutativity* {n} {m})) ]
      === suc (m + (n + m * n)) by[ suc= (associativity+ {m} {n} {m * n}) ]
      === suc (m + suc m * n) by[ refl ]
      === suc m + suc m * n by[ refl ]
      === suc m + n * suc m by[ add= (commutativity* {suc m} {n}) ]
      === suc n * suc m by[ refl ]
