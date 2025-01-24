[On the Algebraic Foundation of Proof Assistants for Intuitionistic Type Theory](https://www.cse.chalmers.se/~abela/flops08.pdf)

Andreas Abel, Thierry Coquand, and Peter Dybjer


原文中 isSu 的定義疑似有誤，以下爲修正後的定義(`subst b cxt` 應爲 `subst b sub`)
```haskell
isSu ∷ Cxt → Cxt → Subst → Bool
isSu cxt []     []         = True
isSu cxt (b:bs) sub@(t:ts) = isSu cxt bs ts &&
                             isTm cxt (subst b sub) t
```
