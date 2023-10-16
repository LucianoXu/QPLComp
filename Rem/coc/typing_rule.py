'''

See (https://coq.inria.fr/refman/language/cic.html#global-environment).

'''


from __future__ import annotations

from .context import *
from .environment import *


################################################################
# rule framework

@meta_term
class MP_WF(MetaProof):
    '''
    well-formed
    ```
        WF(E)[Γ]
    ```
    The proof of well-formed environment and valid contex.
    '''
    def __init__(self, E : Environment, Gamma : Context):
        Meta_Sys_type_check(E, Environment)
        Meta_Sys_type_check(Gamma, Context)
        self.__E = E
        self.__Gamma = Gamma

    @property
    def E(self) -> Environment:
        return self.__E
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma

    def conclusion(self) -> str:
        return f"WF({self.E}){self.Gamma}"
    
@meta_term
class MP_WT(MetaProof):
    '''
    well-typed
    ```
        E[Γ] ⊢ t : T
    ```
    The proof of well-typed term.
    '''
    def __init__(self, E : Environment, Gamma : Context, t : Term, T : Term):
        Meta_Sys_type_check(E, Environment)
        Meta_Sys_type_check(Gamma, Context)
        Meta_Sys_type_check(t, Term)
        Meta_Sys_type_check(T, Term)
        self.__E = E
        self.__Gamma = Gamma
        self.__t = t
        self.__T = T
    
    @property
    def E(self) -> Environment:
        return self.__E
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma
    
    @property
    def t(self) -> Term:
        return self.__t

    @property
    def T(self) -> Term:
        return self.__T
    
    def conclusion(self) -> str:
        return f"{self.E}{self.Gamma} ⊢ {self.t} : {self.T}"


###############################################################
# specific rules

@concrete_term
class MP_W_Empty(MP_WF):
    '''
    W-Empty
    ```
        --------
        WF([])[]
    ```
    '''

    def __init__(self):

        # the conclusion `WF([])[]`
        super().__init__(Environment(), Context())

        
    def premises(self) -> str:
        return ""


@concrete_term
class MP_W_Local_Assum(MP_WF):
    '''
    W-Local-Assum
    ```
        E[Γ] ⊢ T : s
        s ∈ S
        x ∉ Γ
        ------------------------------
        WF(E)[Γ::(x:T)]
    ```
    '''

    def __init__(self, wt : MP_WT, s_sort : MP_IsSort, x_notin_Gamma : MP_Cont_Not_Contain_Var):
        # proof of `E[Γ] ⊢ T : s`
        Meta_Sys_type_check(wt, MP_WT)

        # proof of `s ∈ S`
        Meta_Sys_type_check(s_sort, MP_IsSort)

        # proof of `x ∉ Γ`
        Meta_Sys_type_check(x_notin_Gamma, MP_Cont_Not_Contain_Var)

        # consistent `s`
        if wt.T != s_sort.s:
            raise Meta_Sys_Error("Inconsistent sort.")
        
        # consistent `Γ`
        if wt.Gamma != x_notin_Gamma.Gamma:
            raise Meta_Sys_Error("Inconsistent context.")
        
        self.__wt = wt
        self.__s_sort = s_sort
        self.__x_notin_Gamma = x_notin_Gamma


        # the conclusion `WF(E)[Γ::(x:T)]`
        new_Gamma = x_notin_Gamma.Gamma.push(
            LocalTyping(x_notin_Gamma.var, wt.t)
        )
        super().__init__(wt.E, new_Gamma)
    
    def premises(self) -> str:
        res = self.__wt.conclusion() + "\n"
        res += self.__s_sort.conclusion() + "\n"
        res += self.__x_notin_Gamma.conclusion() + "\n"
        return res

@concrete_term
class MP_W_Local_Def(MP_WF):
    '''
    W-Local-Def
    ```
        E[Γ] ⊢ t : T
        x ∉ Γ
        -------------------------
        WF(E)[Γ::(x:=t:T)]
    ```
    '''

    def __init__(self, wt : MP_WT, x_notin_Gamma : MP_Cont_Not_Contain_Var):

        # proof of `E[Γ] ⊢ t : T`
        Meta_Sys_type_check(wt, MP_WT)

        # proof of `x ∉ Γ`
        Meta_Sys_type_check(x_notin_Gamma, MP_Cont_Not_Contain_Var)

        # consistent `Γ`
        if wt.Gamma != x_notin_Gamma.Gamma:
            raise Meta_Sys_Error("Inconsistent context.")

        self.__wt = wt
        self.__x_notin_Gamma = x_notin_Gamma

        # the conclusion `WF(E)[Γ::(x:=t:T)]`
        new_Gamma = x_notin_Gamma.Gamma.push(
            LocalDef(x_notin_Gamma.var, wt.t, wt.T)
        )
        super().__init__(wt.E, new_Gamma)

    def premises(self) -> str:
        res = self.__wt.conclusion() + "\n"
        res += self.__x_notin_Gamma.conclusion() + "\n"
        return res
    

@concrete_term
class MP_W_Global_Assum(MP_WF):
    '''
    W-Global-Assum
    ```
        E[] ⊢ T : s
        s ∈ S
        c ∉ E
        -------------------------
        WF(E; c:T)
    ```
    '''

    def __init__(self, wt : MP_WT, s_sort : MP_IsSort, c_notin_E : MP_Env_Not_Contain_Const):

        # proof of `E[] ⊢ T : s`
        Meta_Sys_type_check(wt, MP_WT)

        # proof of `s ∈ S`
        Meta_Sys_type_check(s_sort, MP_IsSort)

        # proof of `c ∉ E`
        Meta_Sys_type_check(c_notin_E, MP_Env_Not_Contain_Const)

        # empty Gamma
        if not wt.Gamma.is_empty:
            raise Meta_Sys_Error("Context not empty.")

        # consistent `s`
        if wt.T != s_sort.s:
            raise Meta_Sys_Error("Inconsistent sort.")

        # consistent `E`
        if wt.E != c_notin_E.E:
            raise Meta_Sys_Error("Inconsistent environment.")

        self.__wt = wt
        self.__s_sort = s_sort
        self.__c_notin_E = c_notin_E

        # the conclusion `WF(E; c:T)`
        new_E = wt.E.push(
            GlobalTyping(c_notin_E.const, wt.T)
        )
        super().__init__(new_E, Context())

    def premises(self) -> str:
        res = self.__wt.conclusion() + "\n"
        res += self.__s_sort.conclusion() + "\n"
        res += self.__c_notin_E.conclusion() + "\n"
        return res
    
@concrete_term
class MP_W_Global_Def(MP_WF):
    '''
    W-Global-Def
    ```
        E[] ⊢ t : T
        c ∉ E
        -------------------------
        WF(E; c:=t:T)
    ```
    '''

    def __init__(self, wt : MP_WT, c_notin_E : MP_Env_Not_Contain_Const):

        # proof of `E[] ⊢ t : T`
        Meta_Sys_type_check(wt, MP_WT)

        # proof of `c ∉ E`
        Meta_Sys_type_check(c_notin_E, MP_Env_Not_Contain_Const)

        # empty Gamma
        if not wt.Gamma.is_empty:
            raise Meta_Sys_Error("Context not empty.")

        # consistent `E`
        if wt.E != c_notin_E.E:
            raise Meta_Sys_Error("Inconsistent environment.")

        self.__wt = wt
        self.__c_notin_E = c_notin_E

        # the conclusion `WF(E; c:=t:T)`
        new_E = wt.E.push(
            GlobalDef(c_notin_E.const, wt.t, wt.T)
        )
        super().__init__(new_E, Context())

    def premises(self) -> str:
        res = self.__wt.conclusion() + "\n"
        res += self.__c_notin_E.conclusion() + "\n"
        return res
    

@concrete_term
class MP_Ax_SProp(MP_WT):
    '''
    Ax-SProp
    ```
        WF(E)[Γ]
        -----------------
        E[Γ] ⊢ SProp : Type(1)
    ```
    '''

    def __init__(self, wf : MP_WF):

        # proof of `WF(E)[Γ]`
        Meta_Sys_Error(wf, MP_WF)
        self.__wf = wf

        # the conclusion `E[Γ] ⊢ SProp : Type(1)`
        super().__init__(wf.E, wf.Gamma, SProp(), Type_i(1))
    
    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        return res
    

@concrete_term
class MP_Ax_Prop(MP_WT):
    '''
    Ax-Prop
    ```
        WF(E)[Γ]
        -----------------
        E[Γ] ⊢ Prop : Type(1)
    ```
    '''

    def __init__(self, wf : MP_WF):

        # proof of `WF(E)[Γ]`
        Meta_Sys_Error(wf, MP_WF)
        self.__wf = wf

        # the conclusion `E[Γ] ⊢ Prop : Type(1)`
        super().__init__(wf.E, wf.Gamma, Prop(), Type_i(1))
    
    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        return res
    

@concrete_term
class MP_Ax_Set(MP_WT):
    '''
    Ax-Set
    ```
        WF(E)[Γ]
        -----------------
        E[Γ] ⊢ Set : Type(1)
    ```
    '''

    def __init__(self, wf : MP_WF):

        # proof of `WF(E)[Γ]`
        Meta_Sys_Error(wf, MP_WF)
        self.__wf = wf

        # the conclusion `E[Γ] ⊢ Set : Type(1)`
        super().__init__(wf.E, wf.Gamma, Set(), Type_i(1))
    
    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        return res


@concrete_term
class MP_Ax_Type(MP_WT):
    '''
    Ax-Type
    ```
        WF(E)[Γ]
        ----------------------------
        E[Γ] ⊢ Type(i) : Type(i + 1)
    ```
    '''

    def __init__(self, wf : MP_WF, i : int):

        # proof of `WF(E)[Γ]`
        Meta_Sys_Error(wf, MP_WF)

        # a python number `i`
        Meta_Sys_Error(i, int)
        self.__wf = wf
        self.__i = i

        # the conclusion `E[Γ] ⊢ Type(i) : Type(i + 1)`
        super().__init__(wf.E, wf.Gamma, Type_i(i), Type_i(i+1))
    
    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        return res
    

@concrete_term
class MP_Var(MP_WT):
    '''
    Var
    ```
        WF(E)[Γ]
        (x : T) ∈ Γ or (x:=t : T) ∈ Γ
        -----------------------------
        E[Γ] ⊢ x:T
    ```
    '''

    def __init__(self, wf : MP_WF, x_dec_in_Gamma : MP_Cont_Contain_Typing):

        # proof of `WF(E)[Γ]`
        Meta_Sys_type_check(wf, MP_WF)

        # proo of `(x : T) ∈ Γ` or `(x:=t : T) ∈ Γ`
        Meta_Sys_type_check(x_dec_in_Gamma, MP_Cont_Contain_Typing)

        # consistent `Γ`
        if wf.Gamma != x_dec_in_Gamma.Gamma:
            raise Meta_Sys_Error("Inconsistent context.")
        
        self.__wf = wf
        self.__x_dec_in_Gamma = x_dec_in_Gamma

        # the conclusion `E[Γ] ⊢ x:T`
        super().__init__(wf.E, wf.Gamma, x_dec_in_Gamma.var_typing.x, x_dec_in_Gamma.var_typing.T)


    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        res += self.__x_dec_in_Gamma.conclusion() + "\n"
        return res
    

@concrete_term
class MP_Const(MP_WT):
    '''
    Const
    ```
        WF(E)[Γ]
        (c : T) ∈ E or (c:=t : T) ∈ E
        -----------------------------
        E[Γ] ⊢ c:T
    ```
    '''

    def __init__(self, wf : MP_WF, c_dec_in_E : MP_Env_Contain_Typing):

        # proof of `WF(E)[Γ]`
        Meta_Sys_type_check(wf, MP_WF)

        # proo of `(c : T) ∈ E` or `(c:=t : T) ∈ E`
        Meta_Sys_type_check(c_dec_in_E, MP_Env_Contain_Typing)

        # consistent `E`
        if wf.E != c_dec_in_E.E:
            raise Meta_Sys_Error("Inconsistent environment.")
        
        self.__wf = wf
        self.__c_dec_in_E = c_dec_in_E

        # the conclusion `E[Γ] ⊢ c:T`
        super().__init__(wf.E, wf.Gamma, c_dec_in_E.const_typing.c, c_dec_in_E.const_typing.T)


    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        res += self.__c_dec_in_E.conclusion() + "\n"
        return res
    

@concrete_term
class MP_Prod_SProp(MP_WT):
    '''
    Prod-SProp
    ```
        E[Γ] ⊢ T : s
        s ∈ S
        E[Γ::(x:T)] ⊢ U : SProp
        ---------------------------
        E[Γ] ⊢ ∀x:T, U : SProp
    ```
    '''

    def __init__(self, wt_outer : MP_WT, s_sort : MP_IsSort, wt_inner : MP_WT):

        # proof of `E[Γ] ⊢ T : s`
        Meta_Sys_type_check(wt_outer, MP_WT)

        # proof of `s ∈ S`
        Meta_Sys_type_check(s_sort, MP_IsSort)

        # proof of `E[Γ::(x:T)] ⊢ U : SProp`
        Meta_Sys_type_check(wt_inner, MP_WT)

        # consistent `s`
        if wt_outer.T != s_sort.s:
            raise Meta_Sys_Error("Inconsistent sort.")
        
        # consistent `E`
        if wt_outer.E != wt_inner.E:
            raise Meta_Sys_Error("Inconsistent environment.")
        
        # break `Γ::(x:T)`
        Gamma_pre, dec = wt_inner.Gamma.pop()

        # consistent `Gamma`
        if wt_outer.Gamma != Gamma_pre:
            raise Meta_Sys_Error("Inconsistent context.")
        
        # consistent `T`
        if wt_outer.t != dec.T:
            raise Meta_Sys_Error("Inconssitent 'T'.")
        
        # proof of `U : SProp`
        if wt_inner.T != SProp():
            raise Meta_Sys_Error("Invalid product.")
        
        self.__wt_outer = wt_outer
        self.__s_sort = s_sort
        self.__wt_inner = wt_inner

        # the conclusion `E[Γ] ⊢ ∀x:T, U : SProp`
        prod = Prod(dec.x, dec.T, wt_inner.t)
        super().__init__(wt_outer.E, wt_outer.Gamma, prod, SProp())

    def premises(self) -> str:
        res = self.__wt_outer.conclusion() + "\n"
        res += self.__s_sort.conclusion() + "\n"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    

@concrete_term
class MP_Prod_Prop(MP_WT):
    '''
    Prod-Prop
    ```
        E[Γ] ⊢ T : s
        s ∈ S
        E[Γ::(x:T)] ⊢ U : Prop
        ---------------------------
        E[Γ] ⊢ ∀x:T, U : Prop
    ```
    '''

    def __init__(self, wt_outer : MP_WT, s_sort : MP_IsSort, wt_inner : MP_WT):

        # proof of `E[Γ] ⊢ T : s`
        Meta_Sys_type_check(wt_outer, MP_WT)

        # proof of `s ∈ S`
        Meta_Sys_type_check(s_sort, MP_IsSort)

        # proof of `E[Γ::(x:T)] ⊢ U : Prop`
        Meta_Sys_type_check(wt_inner, MP_WT)

        # consistent `s`
        if wt_outer.T != s_sort.s:
            raise Meta_Sys_Error("Inconsistent sort.")
        
        # consistent `E`
        if wt_outer.E != wt_inner.E:
            raise Meta_Sys_Error("Inconsistent environment.")

        # break `Γ::(x:T)`
        Gamma_pre, dec = wt_inner.Gamma.pop()

        # consistent `Gamma`
        if wt_outer.Gamma != Gamma_pre:
            raise Meta_Sys_Error("Inconsistent context.")
        
        # consistent `T`
        if wt_outer.t != dec.T:
            raise Meta_Sys_Error("Inconssitent 'T'.")
        
        # proof of `U : Prop`
        if wt_inner.T != Prop():
            raise Meta_Sys_Error("Invalid product.")
        
        self.__wt_outer = wt_outer
        self.__s_sort = s_sort
        self.__wt_inner = wt_inner

        # the conclusion `E[Γ] ⊢ ∀x:T, U : Prop`
        prod = Prod(dec.x, dec.T, wt_inner.t)
        super().__init__(wt_outer.E, wt_outer.Gamma, prod, Prop())

    def premises(self) -> str:
        res = self.__wt_outer.conclusion() + "\n"
        res += self.__s_sort.conclusion() + "\n"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    
    
@concrete_term
class MP_Prod_Set(MP_WT):
    '''
    Prod-Set
    ```
        E[Γ] ⊢ T : s
        s ∈ {SProp, Prop, Set}
        E[Γ::(x:T)] ⊢ U : Set
        ---------------------------
        E[Γ] ⊢ ∀x:T, U : Set
    ```
    '''

    def __init__(self, wt_outer : MP_WT, s_sort : MP_IsSort, wt_inner : MP_WT):

        # proof of `E[Γ] ⊢ T : s`
        Meta_Sys_type_check(wt_outer, MP_WT)

        # proof of `s ∈ {SProp, Prop, Set}`
        Meta_Sys_type_check(s_sort, MP_IsSort)
        if not (isinstance(s_sort.s, SProp) or isinstance(s_sort.s, Prop) or isinstance(s_sort.s, Set)):
            raise Meta_Sys_Error("Not satisfied: 's ∈ {SProp, Prop, Set}'.")


        # proof of `E[Γ::(x:T)] ⊢ U : Set`
        Meta_Sys_type_check(wt_inner, MP_WT)

        # consistent `s`
        if wt_outer.T != s_sort.s:
            raise Meta_Sys_Error("Inconsistent sort.")
        
        # consistent `E`
        if wt_outer.E != wt_inner.E:
            raise Meta_Sys_Error("Inconsistent environment.")

        # break `Γ::(x:T)`
        Gamma_pre, dec = wt_inner.Gamma.pop()

        # consistent `Gamma`
        if wt_outer.Gamma != Gamma_pre:
            raise Meta_Sys_Error("Inconsistent context.")
        
        # consistent `T`
        if wt_outer.t != dec.T:
            raise Meta_Sys_Error("Inconssitent 'T'.")
        
        # proof of `U : Set`
        if wt_inner.T != Set():
            raise Meta_Sys_Error("Invalid product.")
        
        self.__wt_outer = wt_outer
        self.__s_sort = s_sort
        self.__wt_inner = wt_inner

        # the conclusion `E[Γ] ⊢ ∀x:T, U : Set`
        prod = Prod(dec.x, dec.T, wt_inner.t)
        super().__init__(wt_outer.E, wt_outer.Gamma, prod, Set())

    def premises(self) -> str:
        res = self.__wt_outer.conclusion() + "\n"
        res += f"{self.__s_sort.s} ∈ {{SProp, Prop, Set}}"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    

@concrete_term
class MP_Prod_Type(MP_WT):
    '''
    Prod-Type
    ```
        E[Γ] ⊢ T : s
        s ∈ {SProp, Type(i)}
        E[Γ::(x:T)] ⊢ U : Type(i)
        ---------------------------
        E[Γ] ⊢ ∀x:T, U : Type(i)
    ```
    '''

    def __init__(self, wt_outer : MP_WT, s_sort : MP_IsSort, wt_inner : MP_WT):

        # proof of `E[Γ] ⊢ T : s`
        Meta_Sys_type_check(wt_outer, MP_WT)

        # proof of `s ∈ {SProp, Type(i)}`
        Meta_Sys_type_check(s_sort, MP_IsSort)
        if not (isinstance(s_sort.s, SProp) or isinstance(s_sort.s, Type)):
            raise Meta_Sys_Error("Not satisfied: 's ∈ {SProp, Type(i)}'.")


        # proof of `E[Γ::(x:T)] ⊢ U : Type(i)`
        Meta_Sys_type_check(wt_inner, MP_WT)

        # consistent `s`
        if wt_outer.T != s_sort.s:
            raise Meta_Sys_Error("Inconsistent sort.")
        
        # consistent `E`
        if wt_outer.E != wt_inner.E:
            raise Meta_Sys_Error("Inconsistent environment.")

        # break `Γ::(x:T)`
        Gamma_pre, dec = wt_inner.Gamma.pop()

        # consistent `Gamma`
        if wt_outer.Gamma != Gamma_pre:
            raise Meta_Sys_Error("Inconsistent context.")
        
        # consistent `T`
        if wt_outer.t != dec.T:
            raise Meta_Sys_Error("Inconssitent 'T'.")
        
        # proof of `U : Type(i)`
        if not isinstance(wt_inner.T, Type_i):
            raise Meta_Sys_Error("Invalid product.")
        
        self.__wt_outer = wt_outer
        self.__s_sort = s_sort
        self.__wt_inner = wt_inner

        # the conclusion `E[Γ] ⊢ ∀x:T, U : Type(i)`
        prod = Prod(dec.x, dec.T, wt_inner.t)
        super().__init__(wt_outer.E, wt_outer.Gamma, prod, wt_inner.T)

    def premises(self) -> str:
        res = self.__wt_outer.conclusion() + "\n"
        res += f"{self.__s_sort.s} ∈ {{SProp, Type(i)}}"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    
    
@concrete_term
class MP_Lam(MP_WT):
    '''
    Lam
    ```
        E[Γ] ⊢ ∀x:T, U : s
        E[Γ::(x:T)] ⊢ t : U
        --------------------
        E[Γ] ⊢ λx:T.t : ∀x:T, U
    ```
    '''

    def __init__(self, wt_outer : MP_WT, wt_inner : MP_WT):

        # proof of `E[Γ] ⊢ ∀x:T, U : s`
        Meta_Sys_type_check(wt_outer, MP_WT)

        # proof of `E[Γ::(x:T)] ⊢ t : U`
        Meta_Sys_type_check(wt_inner, MP_WT)

        # extact `∀x:T, U`
        if not isinstance(wt_outer.t, Prod):
            raise Meta_Sys_Error("Type is not product.")
        
        # break `Γ::(x:T)`
        Gamma_pre, dec = wt_inner.Gamma.pop()

        # consistent `E`
        if wt_outer.E != wt_inner.E:
            raise Meta_Sys_Error("Inconsistent environment.")

        # consistent `Γ`
        if wt_outer.Gamma != Gamma_pre:
            raise Meta_Sys_Error("Inconsistent context.")
    
        # consistent `x`
        if wt_outer.t.x != dec.x:
            raise Meta_Sys_Error("Inconsistent 'x'.")
        
        # consistent `T`
        if wt_outer.t.T != dec.T:
            raise Meta_Sys_Error("Inconsistent 'T'.")
        
        # consistent `U`
        if wt_outer.t.U != wt_inner.T:
            raise Meta_Sys_Error("Inconsistent 'U'.")
        
        self.__wt_outer = wt_outer
        self.__wt_inner = wt_inner

        # the conclusion `E[Γ] ⊢ λx:T.t : ∀x:T, U`
        lam = Abstract(dec.x, dec.T, wt_inner.t)
        prod = Prod(dec.x, dec.T, wt_inner.T)
        super().__init__(wt_outer.E, wt_outer.Gamma, lam, prod)

    def premises(self) -> str:
        res = self.__wt_outer.conclusion() + "\n"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    

@concrete_term
class MP_App(MP_WT):
    '''
    App
    ```
        E[Γ] ⊢ t: ∀x:U, T
        E[Γ] ⊢ u : U
        --------------------
        E[Γ] ⊢ (t u) : T{x/u}
    ```
    '''

    def __init__(self, wt_t : MP_WT, wt_u : MP_WT):

        # proof of `E[Γ] ⊢ t: ∀x:U, T`
        Meta_Sys_type_check(wt_t, MP_WT)

        # proof of `E[Γ] ⊢ u : U`
        Meta_Sys_type_check(wt_u, MP_WT)

        # extact `∀x:U, T`
        if not isinstance(wt_t.T, Prod):
            raise Meta_Sys_Error("Invalid 't' type.")
        
        # consistent `E`
        if wt_t.E != wt_u.E:
            raise Meta_Sys_Error("Inconsistent environment.")

        # consistent `Γ`
        if wt_t.Gamma != wt_u.Gamma:
            raise Meta_Sys_Error("Inconsistent context.")
        
        # consistent `U`
        if wt_t.T.T != wt_u.T:
            raise Meta_Sys_Error("Inconsistent 'U'.")
        
        self.__wt_t = wt_t
        self.__wt_u = wt_u

        # the conclusion `E[Γ] ⊢ (t u) : T{x/u}`
        app = Apply(wt_t.t, wt_u.t)
        T_sub = wt_t.T.U.substitute(wt_t.T.x, wt_u.t)
        super().__init__(wt_t.E, wt_t.Gamma, app, T_sub)

    def premises(self) -> str:
        res = self.__wt_t.conclusion() + "\n"
        res += self.__wt_u.conclusion() + "\n"
        return res
    

@concrete_term
class MP_Let(MP_WT):
    '''
    Let
    ```
        E[Γ] ⊢ t : T
        E[Γ::(x:=t:T)] ⊢ u : U
        --------------------
        E[Γ] ⊢ let x:=t:T in u : U{x/t}
    ```
    '''

    def __init__(self, wt_outer : MP_WT, wt_inner : MP_WT):

        # proof of `E[Γ] ⊢ t : T`
        Meta_Sys_type_check(wt_outer, MP_WT)

        # proof of `E[Γ::(x:=t:T)] ⊢ u : U`
        Meta_Sys_type_check(wt_inner, MP_WT)

        
        # break `Γ::(x:=t:T)`
        Gamma_pre, dec = wt_inner.Gamma.pop()
        if not isinstance(dec, LocalDef):
            raise Meta_Sys_Error("Invalid context.")

        # consistent `E`
        if wt_outer.E != wt_inner.E:
            raise Meta_Sys_Error("Inconsistent environment.")

        # consistent `Γ`
        if wt_outer.Gamma != Gamma_pre:
            raise Meta_Sys_Error("Inconsistent context.")

        # consistent `t`
        if dec.t != wt_outer.t:
            raise Meta_Sys_Error("Inconsistent 't'.")

        # consistent `T`
        if wt_outer.T != dec.T:
            raise Meta_Sys_Error("Inconsistent 'T'.")
        
        self.__wt_outer = wt_outer
        self.__wt_inner = wt_inner

        # the conclusion `E[Γ] ⊢ let x:=t:T in u : U{x/t}`
        let_in = Let_in(dec.x, dec.t, dec.T, wt_inner.t)
        U_sub = wt_inner.T.substitute(dec.x, dec.t)
        super().__init__(wt_outer.E, wt_outer.Gamma, let_in, U_sub)

    def premises(self) -> str:
        res = self.__wt_outer.conclusion() + "\n"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    

# basic typing rules ends here
#####################################################

