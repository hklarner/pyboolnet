

from pyboolnet.boolean_logic import minimize_espresso


def test_minimize_espresso1():
    expression = "1"
    expected = "1"
    answer = minimize_espresso(expression)
    
    assert answer == expected

    expression = "(a & b) | a"
    expected = "(a)"
    answer = minimize_espresso(expression, Merge=True, Equiv=True, Exact=True, Reduce=True)
    
    assert answer == expected

    expression = "Test = STMNCanAct & (STMN & ((Cytokinesis & ((MTCanAct | (MT)) | !GSK3B) | !Cytokinesis & (((MTCanAct | (MT)) | !GSK3B) | !CentrosomeMat)) | !PLK1) | !STMN & ((((MTCanAct | (MT)) | !GSK3B) | !CentrosomeMat) | !PLK1)) | !STMNCanAct & (((((MTCanAct | (MT)) | !GSK3B) | !Cytokinesis) | !PLK1) | !STMN);"
    expected = "Test = (!Cytokinesis & !CentrosomeMat) | (!GSK3B) | (MT) | (MTCanAct) | (!STMN & !CentrosomeMat) | (!PLK1) | (!STMNCanAct & !Cytokinesis) | (!STMNCanAct & !STMN);"
    answer = minimize_espresso(expression)

    assert answer == expected


def test_minimize_espresso2():
    expression = "a | !a"
    expected = "1"
    answer = minimize_espresso(expression, Merge=True, Equiv=True, Exact=True, Reduce=True)
    
    assert answer == expected


def test_minimize_espresso3():
    expression = "a & !a&!a"
    expected = "0"
    answer = minimize_espresso(expression, Merge=True, Equiv=True, Exact=True, Reduce=True)
    
    assert answer == expected


def test_minimize_espresso4():
    expression = "a&b | a | !a"
    expected = "1"
    answer = minimize_espresso(expression, Merge=True, Equiv=True, Exact=True, Reduce=True)
    
    assert answer == expected


def test_minimize_espresso5():
    expression = "1&a"
    expected = "(a)"
    answer = minimize_espresso(expression, Merge=True, Equiv=True, Exact=True, Reduce=True)
    
    assert answer == expected

