# Judgments-as-types
Using dependent types as a metalanguage with Idris2.

You can use a dependently typed language like Idris, Agda, Coq (gallina?), etc. as a metalangue for reasoning about 
formal systems (propositional logic, FOL, hoare logic, simply typed lambda calculus, etc.).  
This idea is the core of the Edinburgh Logical Framework (ELF).

## Curry-Howard 2.0
| **Formal system**         | **Type theory** | **Marketing name**       |
|---------------------------|-----------------|--------------------------|
| theorem (formula)         | type            | _propositions-as-types_  |
| proof                     | term            | _proofs-as-programs_     |
| judgment (inference rule) | type            | _judgments-as-types_     |

# Propositional (classical) logic 

### Syntax

$$
 e \ ::= \ \neg e \ | \  e \Rightarrow e \ | \ e \wedge e 
$$

In idris is
 
```idris
data Formula : Type where
  Neg : Formula -> Formula
  Imp : Formula -> Formula -> Formula
  And : Formula -> Formula -> Formula

```

### Set of proofs 

We define that the set of proofs of a formula   $T(\phi) =$  { proof  | proof of $\phi$ } is inductively defined by judgments. 

In idris:
```idris
data T : Formula -> Type where
 -- The constructors of this inductive dependent type are the judgments of natural deduction  
```
Note that $t$ is a proof of $\phi$ if $t \in T(\phi)$ or, using Curry-Howard and Idris notation, if t : T ϕ

Lets define the judgments as constructors of the type T  
$\phi$  
▁ ( $Ident$ )  
$\phi$  
```idris
  Ident : T ϕ -> T ϕ
```

------------

  [ $\phi$ ]                          
    ⋮  
  $\psi$                            
  ───    ( $ImpI$ )  
  $\phi \Rightarrow \psi$
 
 
 
 &nbsp;
 
 
  $\phi \Rightarrow \psi \ \ \ \ \ \ \phi $                                   
  ────── ( $ImpE$ )  
  $\psi$ 


```idris
  ImpI : (T ϕ -> T Ψ) -> T (ϕ `Imp` Ψ)
  
  ImpE : T (ϕ `Imp` Ψ) -> T ϕ -> T Ψ
```

------------
 
  $\phi \ \ \ \ \ \ \psi $                                   
  ──── ( $AndI$ )  
  $\phi \wedge \psi$ 
  
  &nbsp;
  
  
  $\phi \wedge \psi $                                   
  ──── ( $AndE1$ )  
  $\phi$ 
  
 &nbsp;
  
  
  $\phi \wedge \psi $                                   
  ──── ( $AndE1$ )  
  $\psi$ 
  

```idris
  AndI : T ϕ -> T Ψ -> T (ϕ `And` Ψ)
      
  AndE1 : T (ϕ `And` Ψ) -> T ϕ
       
  AndE2 : T (ϕ `And` Ψ) -> T Ψ
```

-----------

   $\[\phi\] \ \ \ \ \ \ \[\phi\]$                           
    $⋮            \ \ \ \ \ \ \ \ \ \      ⋮$  
  $\psi  \ \ \ \ \ \ \ \neg \psi$                            
  ────    ( $NegI$ )  
  $\neg \phi$
  
 &nbsp;
 
 $\neg \neg \phi$                            
 ──    ( $NegI$ )  
 $\phi$



```idris
  NegI : (T ϕ -> T Ψ) -> (T ϕ -> T (Neg Ψ)) -> T (Neg ϕ)  
  NegE : T (Neg $ Neg ϕ) -> T ϕ
```

### Proofs examples
Lets prove $(P \Rightarrow P)$, $(P \wedge Q \Rightarrow P)$ and $(P \wedge Q \Rightarrow Q)$
```idris

P, Q, R : Formula

proof1 : T (P `Imp` P)
proof1 = ImpI Ident


proof2 : T ((P `And` Q) `Imp` P)
proof2 = ImpI AndE1


proof3 : T ((P `And` Q) `Imp` Q)
proof3 = ImpI AndE2
```
For better understanding draw the natural deduction proof tree, the judgments names that are used are  
what you see in the terms (proofs) `proof1`, `proof2` and `proof3`. 
&nbsp;

Notice something, we are proving using dependent type theory as a metalanguage (propositional classical logic is the object language).  
It's not the same as proving using directly Curry-Howard. This would be the proofs using just Curry-Howard, notice the difference.

```idris
proof1 : { P : Type } -> P -> P
proof1 p = p

proof2 : { P , Q : Type } -> (P, Q) -> P
proof2 (a, b) = a

proof3 : { P, Q : Type } -> (P, Q) -> Q
proof3 (a, b) = b


```
The types here corresponds to formulas of an intuisionistic higer order logic. 

# First order logic

# Cheat sheet
This is in spanish, so if you can't read it just learn spanish 👍  
![alt text](Parte0.jpeg)
![alt text](Parte1.jpeg)



# Bibliography
- Avron, Arnon & Honsell, Furio & Mason, Ian. (1996). An Overview of the Edinburgh Logical Framework. 10.1007/978-1-4612-3658-0_8. 
