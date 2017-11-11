# compiler.py

def compiler(tokenGen):
    for tok in tokenGen:
        print(tok)

if __name__=="__main__":
    import lexer
    global ast
    ast = compiler(lexer.lexer("src/wombat.wh"))
    print(ast)
