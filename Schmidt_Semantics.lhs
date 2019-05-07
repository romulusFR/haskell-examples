%  lhs2TeX Schmidt_Semantics.lhs > Schmidt_Semantics.tex && pdflatex Schmidt_Semantics.tex

\documentclass[a4paper]{article}
  \usepackage[utf8]{inputenc}
  \usepackage[T1]{fontenc}
  \usepackage{textcomp}
  \usepackage{xspace}
  \usepackage{mdwlist}
  \usepackage{url}
  \usepackage[bookmarksnumbered]{hyperref}
  \hypersetup{
    pdftitle={Programming language semantics},
    pdfauthor={Romuald THION, David A. Schmidt},
    pdfsubject={http://people.cis.ksu.edu/~schmidt/papers/CRC.chapter.ps.gz},
    pdfkeywords={Denotational semantics, imperative language, toy example, language implementation}
  }

  %Pretty printing for lhs2TeX
  %include lhs2TeX.fmt
  %include forall.fmt
  %options ghci -Wall
  %include ./lhs2TeX-typesetting.tex
  %let visible=False

  \newcommand{\cat}[1]{\ensuremath{\mathbf{#1}}\xspace}
  \newcommand{\SET}{\cat{Set}}
  \newcommand{\bbfont}[1]{\mathbb{#1}} % typo blackboard
  \newcommand{\BB}{\ensuremath{\bbfont{B}}\xspace} %	booléens
  \newcommand{\NN}{\ensuremath{\bbfont{N}}\xspace} %	nombres naturels
  \newcommand{\true}{\ensuremath{\mathbf{tt}}\xspace} %	booléens
  \newcommand{\false}{\ensuremath{\mathbf{ff}}\xspace} %	booléens

\author{Romuald \textsc{Thion}}
\title{Programming language semantics}
\date{2012}

\begin{document}
  \maketitle

  \begin{abstract}
Haskell implementation of the denotational semantics for the toy programming language in David A. \textsc{Schmidt}'s~\cite{Schmidt97}, available at
\url{http://people.cis.ksu.edu/~schmidt/papers/CRC.chapter.ps.gz}

  \end{abstract} 

%if visible

> {-# OPTIONS -Wall #-}
> {-# OPTIONS -fwarn-tabs #-}
> {-# OPTIONS -fwarn-incomplete-record-updates #-}
> {-# OPTIONS -fwarn-monomorphism-restriction #-}
> {-# OPTIONS -fno-warn-unused-imports #-}
>
> {-# LANGUAGE TypeSynonymInstances #-} 
>
> module Semantic where
>
> import Data.Function (fix)
>
> type Nat = Integer
> type Id = String
>
> bot :: a
> bot = undefined

%endif

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}\label{sec:intro}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


This program is written in the Literate Haskell style.
It compile with both a \LaTeX and a Haskell compiler with the literate features turned on :
\begin{itemize}
    \item  The Glasgow Haskell Compiler do supports this source style (\texttt{.lhs} file extension). The slogan is ``everything is comment, please use |>| before a line of code''.
    \item |lhs2TeX| is used as a frontend for |pdflatex|.A config file is used to typeset the code according to \textsc{Schmidt}'s mathematical notational conventions.
\end{itemize}

To compile, use the following command line
\begin{verbatim}
lhs2TeX Schmidt_Semantics.lhs > Schmidt_Semantics.tex
  && rubber --warn all --pdf Schmidt_Semantics.tex
\end{verbatim}

The document is a quite direct implementation of David A. \textsc{Schmidt}'s semantics for a toy programming language~\cite{Schmidt97}, freely available on the internet~\footnote{\url{http://people.cis.ksu.edu/~schmidt/papers/CRC.chapter.ps.gz}}.
The paper focuses on denotional semantics, its includes a detailled example for a toy imperative language.

The interpreter is built quite closely from the mathematical definitions in pages 6 to 11 of~\cite{Schmidt97}.
The main differences with the paper are:
\begin{itemize}
    \item the \texttt{Maybe} monad is used for $\bot$,
    \item the intepreter returns a store instead of a single integer,
    \item coproduct $+$ is used instead of $\NN \cup \{\true, \false\}$,
     \item some extra tests has been added for borderline cases,
    \item fixpoint combinator |fix| is used for denotation of while construction. Actually, it's the only tricky part of the code.    
\end{itemize}


It has been written in a hurry an should be improved!
The document is meant to compile without warning with full strictures turned on.


\section{Syntax}

Notational conventions.

\begin{itemize*}
    \item composition is \eval{:t (.)}

    \item on types:
        \begin{itemize*}
            \item boolean domain is written |Bool={True, False}|,
            \item integers are written |Integer|,
            \item |Maybe A| is an optional |A| that is  $\mu X.1 + A$. In \SET, it is |Maybe A|$=A \cup \{ * \}$
        \end{itemize*}

\end{itemize*}


The syntax of the toy imperative language

> data Prog = Prog Comm
>
> data Comm =    Affect Id Expr 
>              | Sequence Comm Comm
>              | Begin Decl Comm
>              | Call Id
>              | While Expr Comm
> data Decl = ProcDef Id Comm
>
> data Expr = Val Nat
>           | Add Expr Expr
>           | NotEq Expr Expr
>           | Var Id


\section{Domain}

A triple to store values of variables "X","Y" and "Z"

> type Store = (Nat,Nat,Nat)
> data Loc = A | B | C
> look :: Loc -> Store -> Nat
> look A  (x,_,_)  = x
> look B  (_,y,_)  = y
> look C  (_,_,z)  = z

> update :: Loc -> Nat -> Store -> Store
> update A i  (_,y,z)  = (i,y,z)
> update B i  (x,_,z)  = (x,i,z)
> update C i  (x,y,_)  = (x,y,i)

> initStore :: Nat -> Store
> initStore n = (n,0,0)

Environment, that maps identifiers to either a location or a function that modifies the store.
The Maybe monad is used to capture bottom, |check| function is |bind| |(>>=)| with parameters reversed.

> check :: (Store -> Maybe Store) -> Maybe Store -> Maybe Store
> check f s = s >>= f

> data Denotable = Mem Loc | Fun (Store -> Maybe Store)
> type Env = [(Id,Denotable)]

> find :: Id -> Env -> Denotable
> find _ []         = error "find: Empty environnement"
> find i ((j,d):es)  | (i == j)   = d
>                    | otherwise  = find i es
> 
> bind :: Id -> Denotable -> Env -> Env
> bind =  ((.) . (.))  (:) (,)

|bind| is written in a cryptic way. Please consider this definition |bind i d e = (i,d):e|.

>
> initEnv :: Env
> initEnv = ("X",Mem A):("Y",Mem B):("Z",Mem C):[]

\section{Denotation}

Semantic mappings for each level of the syntax
\begin{itemize}
    \item |denotP| for Prog(rams)
    \item |denotD| for Decl(arations)
    \item |denotC| for Comm(ands)
    \item |denotE| for Expr(essions)
\end{itemize}

\subsection{Programs}

Piece of cake.

> denotP :: Prog -> Nat -> Maybe Store
> denotP (Prog c) = \n -> (denotC c) initEnv (initStore n)

\subsection{Declarations}

A declaration is mapped to an endo function of the environment.

> denotD :: Decl -> Env -> Env
> denotD (ProcDef i c) = \e -> bind i (Fun (denotC c e)) e

\subsection{Commands}

> denotC :: Comm -> Env -> Store -> Maybe Store
> denotC  (Affect i x)    = \e s  -> case (find i e) of
>                                Mem l   -> case (denotE x e s) of
>                                                Left v   -> Just (update l v s)
>                                                Right _  -> fail "denotC: Nat expected"
>                                Fun _   -> fail "denotC: Location expected"
> denotC  (Sequence x y)  = \e s  -> (denotC x e s) >>= (denotC y e)
> denotC  (Begin d c)     = \e s  -> denotC c (denotD d e) s
> denotC  (Call i)        = \e  -> case (find i e) of
>                                    Mem _   -> const (fail "denotC: Fun expected")
>                                    Fun f   -> f
> denotC  (While x c)     = \e ->  let 
>    f :: (Store -> Maybe Store) -> (Store -> Maybe Store)
>    f h = \s -> case (denotE x e s) of
>           (Right True)   -> (denotC c e s) >>= h
>           (Right False)  -> Just s
>           (Left _)       -> fail "denotC: Bool expected"
>                           in fix f 

\subsection{Expressions}

Function \eval{:t fix} defined as |fix f = let x = f x in x| is the fixed point\footnote{\url{http://en.wikibooks.org/wiki/Haskell/Denotational_semantics}} combinator of Haskell

> denotE :: Expr -> Env -> Store -> Either Nat Bool
> denotE (Val i)      = \_ _ -> Left i
> denotE (Var x)      = \e s -> case (find x e) of
>                                Mem l   -> Left $ look l s
>                                Fun _   -> error "denotE: Location expected"
> denotE (Add x y)    = \e s -> case (denotE x e s,denotE y e s) of
>                                    (Left x', Left y') -> Left (x' + y')
>                                    _                  -> error "denotE: Nat expected"
> denotE (NotEq x y)  = \e s -> case (denotE x e s,denotE y e s) of
>                                    (Right x', Right y') -> Right (x' /= y')
>                                    (Left x', Left y')   -> Right (x' /= y')
>                                    _                    -> error "denotE: Bool VS Nat"

\section{Toy sample}

The toy sample of the paper: a function that squares a natural number.

> myDecl :: Decl
> myDecl = ProcDef "INCR" aComm where
>   aComm, comm1, comm2 :: Comm
>   aComm = Sequence comm1 comm2 
>   comm1 = Affect "Z" (Add (Var "Z") (Var "X"))
>   comm2 = Affect "Y" (Add (Var "Y") (Val 1))
>
> myBody :: Comm
> myBody = Sequence initP aLoop where
>   initP,aLoop :: Comm
>   initP = Sequence (Affect "Y" (Val 0)) (Affect "Z" (Val 0))
>   aLoop = While cond inn
>   cond :: Expr
>   cond = NotEq (Var "Y") (Var "X")
>   inn :: Comm
>   inn = Call "INCR"
>
> myProg :: Prog
> myProg = Prog (Begin myDecl myBody) 

Instances of class |Show| are defined in the source files (pretty printing).

%= "begin proc INCR = Z:=Z + X; Y:=Y + 1 in Y:=0; Z:=0; while Y != X do call INCR od end."
\begin{center}|show myProg| = \eval{show myProg}\end{center}

One can use |denotP| as an interpreter for the programming language

\begin{center}|denotP myProg 9| = \eval{denotP myProg 9}\end{center}

More generally, for $x\geq 0$, |denotP myProg x = Just (x,x,x^2)|.

%if visible

> instance Show Prog where
>   show (Prog x) = show x ++ "."
>
> instance Show Comm where
>   show (Affect i e) = i ++ ":=" ++ (show e)
>   show (Sequence x y) = show x ++ "; " ++ show y
>   show (Begin d c)  = "begin " ++ show d ++ " in " ++ show c ++ " end"
>   show (Call i)     = "call " ++ i
>   show (While e c)  = "while " ++ show e ++ " do " ++ show c ++ " od"
>
> instance Show Decl where
>   show (ProcDef i c) = "proc " ++ i ++ " = " ++ show c
>
> instance Show Expr where
>   show (Val i) = show i
>   show (Var x) = x
>   show (Add x y) = show x ++ " + " ++ show y
>   show (NotEq x y) = show x ++ " != " ++ show y

%endif

  \bibliographystyle{alpha}
  \bibliography{Schmidt_Semantics}
\end{document}


