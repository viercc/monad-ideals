# Revision history for monad-ideals

## 0.1.1.0 -- 2024-07-30

* List GHC 9.10.* as supported

* Add Foldable and Traversable instances to coproduct `(:+)` and product `(:*)`

## 0.1.0.0 -- 2024-04-23

* Created based on [category-extras-0.53.5](https://hackage.haskell.org/package/category-extras-0.53.5)
  with updates

  - Changes needed to work with current ecosystem
  - Implement coproduct of ideal monads (product of coideal comonads)