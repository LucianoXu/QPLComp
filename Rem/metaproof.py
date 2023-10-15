
class MetaProof:
    '''
    The proof objects for CIC calculus itself.
    '''
    rule_name = "natural"

    def premises(self) -> str:
        raise NotImplementedError()
    
    def conclusion(self) -> str:
        raise NotImplementedError()
    
    def __str__(self) -> str:
        space_len = len(self.rule_name) + 3

        # indent, premise
        res = " " * space_len + self.premises()
        if res[-1] == "\n":
            res = res[:-1]
        res = res.replace("\n", "\n" + " " * space_len)
        res += "\n"

        # line
        res += f"({self.rule_name}) " + "-"*40 + "\n" 

        # indent conclusion
        res += " " * space_len + self.conclusion() 
        return res