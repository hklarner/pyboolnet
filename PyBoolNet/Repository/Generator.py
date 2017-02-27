

def isolated_circuit(N, Sign, FnameBNET=None):
    """
    Creates a *bnet* file of an isolated circuit of length *N* and given *Sign*.

    **arguments**:
       * *N* (int): number of components
       * *Sign* (str): either *"positive"* or *"negative"*
       * *FnameBNET* (str): name of *bnet* file or *None* for the string of the file contents

    **returns**:
        * *BNET* (str) if *FnameBNET=None* or *None* otherwise

    **example**::
    
          >>> isolated_circuit(3, "positive")
          v1,  v2
          v2,  v3
          v3,  v1
    """
    Sign = Sign.lower()
    assert( Sign in ["positive","negative"])

    lines = ["v%i, \t v%i"%(i,i+1) for i in range(1,N)]
    if Sign=="positive":
        lines+= ["v%i, \t v1"%N]
    else:
        lines+= ["v%i, \t !v1"%N]

    if FnameBNET==None:
        return "\n".join(lines)
    else:
        with open(FnameBNET, "w") as f:
            f.writelines("\n".join(lines))
