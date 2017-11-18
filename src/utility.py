def die(s,fn,lineNum,pos):
    raise Exception(s+" in "+fn+"("+str(lineNum)+"/"+str(pos)+")")

def unquote(s): # remove leading/trailing " and convert \\ to \ and \" to "
    assert s[0]=='"' and s[-1]=='"' and s[1]!='"' and s[-2]!='\\' and not re.search(r'[^\\]"',s[1:-1])
    return re.sub(r'\\(.)',r'\1',s[1:-1])

