# Judgments-as-types
Using dependent types as a metalanguage with Idris2.

You can use a dependently typed language like Idris, Agda, Coq (gallina?), etc. as a metalangue for reasoning about 
formal systems (propositional logic, FOL, hoare logic, simply typed lambda calculus, etc.).  
This idea is the core of the Edinburgh Logical Framework (ELF).

## Curry-Howard 2.0
| **Formal system**         | **Type theory** | **Marketing name**       |
|---------------------------|-----------------|--------------------------|
| theorem (formula)         | type            | _propositions-as-types_  |
| proof                     | term            | _proofs-as-types_        |
| judgment (inference rule) | type            | _judgments-as-types_      |

# Propositional logic

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

We define that the set of proofs of a formula   $T(\varphi) =$  { proof  | proof of $\varphi$ } is inductively defined by judgments. 

$\varphi$  
▁ ( $ident$ )  
$\varphi$  

# First order logic

# Cheat sheet
This is in spanish, so if you can't read it just learn spanish 👍  
![alt text](Parte0.jpeg)
![alt text](Parte1.jpeg)



# Bibliography
- Avron, Arnon & Honsell, Furio & Mason, Ian. (1996). An Overview of the Edinburgh Logical Framework. 10.1007/978-1-4612-3658-0_8. 
