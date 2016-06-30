


try:
    # Python 2.x
    import ConfigParser as configparser
    
except ImportError:
    # Python 3.x
    import configparser

myconfigparser = configparser



import math

# auxillary to create graph labels that are as square as possible
# used by e.g. stg2sccgraph / stg2condensationgraph / basin diagram

def divide_list_into_similar_length_lists(List):
    """
    used for drawing pretty labels.
    """
    
    width = sum(len(x) for x in List)
    width = math.sqrt(width)

    stack = list(List)
    lists = []
    remaining = sum(map(len,stack))
    while remaining>width:
        new  = stack.pop()
        size = len(new)
        line = [new]
        while size<width:
            new = stack.pop()
            size+=len(new)
            line+=[new]
        lists.append(line)
        remaining = sum(map(len,stack))
    if stack:
        lists.append(stack)

    return lists
