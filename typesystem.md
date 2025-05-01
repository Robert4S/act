# Sorts
* (Type) : Sort of expressions
□ (Kind) : Sort of types
# Formation rules
* -> * : Functions (Only actors at this point)
□ -> □ : Type Constructors
□ -> * : Polymorphic terms
# Ideas
## Type classes and instances modeled as dependent types instead of dictionary values
**K is a new proposed sort**
K : Sort of Constraint kinds
**A new formation rule is proposed to allow Constraints to depend on types**
□ -> K
A type class is a dependent type abstraction with a dependent constraint kind on the right side of the arrow in its kind signature;
```
class Functor f :: (f:: * -> * ) -> Constraint(Functor, f) {
   fmap : f a -> (a -> b) -> f b
}
```
And creating an instance of a class `F` for type `a` is creating a type with kind `Constraint(F, a)` by applying the type constructor underpinning the class `F` to type `a` and providing proof of `a` implementing the methods defined in `F`;

```
type FunctorList :: Constraint(Functor, List) = instance Functor List {
   fmap Nil f = Nil
   fmap (x:xs) f = (f x):(fmap xs f)
}
```
And when a term requires a type to implement a class, a type variable is introduced with the kind of that constraint, and for that variable to be eliminated in order to expose the unabstracted term, a type of that constraint kind must obviously exist, because it must be applied, so there must exist an implementation of the class methods for that type;
```
polyfmap : (
        (Π(f::* -> *). Π(ff::Constraint(Functor, f)). Π(a::*). Π(b::*). (f a -> (a -> b) -> f b))
    ::  (f::(* -> *) -> Constraint(Functor, f) -> * -> * -> *)
    )
polyfmap [f::*->*] [ff::Constraint(Functor, f)] [a::*] [b::*] (fa: f a) (f: a -> b) = ff.fmap fa f
```
and to be able to use `polyfmap`, a type which satisfies (has the kind of) the constraint must be constructed first, which guarantees it implements the methods, so;
```
(polyfmap [List] [FunctorList] [Int] [Int] (1::2::3::Nil) id) : List Int
```
Is well formed.
