def die(s,fn,lineNum,pos):
    raise Exception(s+" in "+fn+"("+str(lineNum)+"/"+str(pos)+")")

import re

def unquote(s): # remove leading/trailing " and convert \\ to \ and \" to "
    if s==None: return None
    assert s[0]=='"' and s[-1]=='"' and s[1]!='"' and s[-2]!='\\' and re.search(r'[^\\]"',s[1:-1])==None
    return re.sub(r'\\(.)',r'\1',s[1:-1])

