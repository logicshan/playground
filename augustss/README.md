An exercise in dependent types: A well-typed interpreter

文章中 extendT 和 extendV 的定義疑似有誤(錯誤不止這些，此兩處很隱蔽)

```agda
extendT : TEnv → Symbol → Type → TEnv
extendT g x t = λ(x' : Symbol) → if (x' == x) then t else (g x')
--                                                           ^

extendV : (g : TEnv) →
          (r : VEnv g) →
          (x : Symbol) →
          (t : Type) →
          (v : Decode t) →
          (VEnv (extendT g x t))
extendV g r x t v = λ(x' : Symbol) → IF (x' == x) v (r x')
--                                                     ^

```
