#!/usr/bin/env python
# -*- coding: utf-8 -*-
# Autor: Caio Cesar Hideo Nakai
import os

# os.environ["PATH"] += os.pathsep + 'C:/Program Files/Graphviz2.38/bin/'
from subprocess import call

from anytree import AnyNode, Node, RenderTree
from anytree.render import AsciiStyle, DoubleStyle
from anytree.exporter import DotExporter
from graphviz import Graph, Digraph
from nani import aleatorio as arv_reduzida

import argparse
import sys
import ply.lex as lex
import ply.yacc as yacc
import logging
import numbers

from llvmlite import ir

# listas que armazenam dados para tratamento de erro léxico
FECHA_CHAVES_SOLO = []
ABRE_CHAVES_LINHA = []
CARACTERES_INVALIDOS = []

# variavel sucesso analise sintática
ERRO_SINTATICO = False

# palavras reservadas da linguagem são definidas aqui
palavras_reservadas = {
    'se': 'SE',
    'senão': 'SENAO',
    'então': 'ENTAO',
    'retorna': 'RETORNA',
    'repita': 'REPITA',
    'até': 'ATE',
    'leia': 'LEIA',
    'escreva': 'ESCREVA',
    'fim': 'FIM',
    'inteiro': 'TIPO_INTEIRO',
    'flutuante': 'TIPO_FLUTUANTE',
}

# definição dos tokens utilizados
tokens = ['INTEIRO',
          'FLUTUANTE',
          'MAIS',
          'MENOS',
          'DIVIDIDO',
          'ATRIBUIR',
          'MULTIPLICA',
          'IDENTIFICADOR',
          'FECHA_CHAVES_SOLO',
          'ABRE_PARENTESES',
          'FECHA_PARENTESES',
          'MAIOR',
          'MENOR',
          'MAIOR_IGUAL',
          'MENOR_IGUAL',
          'DIFERENTE',
          'DOIS_PONTOS',
          'VIRGULA',
          'IGUAL',
          'ABRE_COLCHETES',
          'FECHA_COLCHETES',
          'NOVA_LINHA',
          'E_LOGICO',
          'OU_LOGICO',
          ] + list(palavras_reservadas.values())  # concatenação com a lista de palavras reservadas!

# as variáveis precisam obrigatoriamente ter o mesmo nome dado na definição acima!
t_ignore = ' \t'
t_MAIS = r'\+'
t_MENOS = r'\-'
t_MULTIPLICA = r'\*'
t_DIVIDIDO = r'/'
t_VIRGULA = r','
t_ABRE_PARENTESES = r'\('
t_FECHA_PARENTESES = r'\)'
t_ABRE_COLCHETES = r'\['
t_FECHA_COLCHETES = r'\]'
t_ATRIBUIR = r'\:='
t_IGUAL = r'='
t_DOIS_PONTOS = r':'
t_MAIOR_IGUAL = r'\>='
t_MENOR_IGUAL = r'\<='
t_MAIOR = r'\>'
t_MENOR = r'\<'
t_DIFERENTE = r'<>'
# t_OU_LOGICO =        r'||'
t_E_LOGICO = r'&&'

# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~  INÍCIO DO TRATAMENTO DE COMENTÁRIO ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

t_COMENTARIO_ignore = r'+ - * / , ( ) [ ] := >= <= > < ='

# definição do estado de comentário
states = (
    ("COMENTARIO", "inclusive"),
)


# quando ler "{" troca o estado para 'COMENTARIO'
def t_start_comentario(t):
    r'\{'
    # coloca a posicao da linha do abre chaves em uma lista
    ABRE_CHAVES_LINHA.append(t.lineno)
    t.lexer.push_state('COMENTARIO')


# contador  de linhas enquanto está no estado comentario
def t_COMENTARIO_newline(t):
    r'\n'
    t.lexer.lineno += 1


# ignora tab
def t_COMENTARIO_tab(t):
    r'\t'


# ignora -> expressão regular para leitura de números ponto flutuante
def t_COMENTARIO_flut(t):
    r'\d+\.\d+ | \d+[eE][-+]\d+'


# ignora -> expressão regular para leitura de números naturais
def t_COMENTARIO_int(t):
    r'\d+'


# ignora -> textos
def t_COMENTARIO_ident(t):
    r'[a-zA-ZÀ-ÿ_][a-zA-ZÀ-ÿ_0-9]*'


# quando encontra '}' sai do estado 'COMENTARIO'
def t_COMENTARIO_end(t):
    r'\}'
    if (ABRE_CHAVES_LINHA):
        ABRE_CHAVES_LINHA.pop()
    t.lexer.pop_state()


# se encontrar algum caractere diferente dos caracteres definidos acima, exibe a mensagem de erro
def t_COMENTARIO_error(t):
    # print("Caractere invalido no comentario'%s' linha %s" %(t.value[0], t.lineno))
    t.lexer.skip(1)


# conteúdo do comentário, ignora tudo q é diferente de '}' essa abordagem não conta linhas enquanto esta no
# estado COMENTARIO.
# def t_COMENTARIO_conteudo(t):
# 	r'[^}]+'


# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~  FIM DO TRATAMENTO DE COMENTÁRIO ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ EXPRESSÕES REGULARES PARA LEITURA DOS TOKENS ~~~~~~~~~~~~~~~~~

# expressão regular para leitura de identificadores (nome de função/variável)
def t_IDENTIFICADOR(t):
    r'[a-zA-ZÀ-ÿ_][a-zA-ZÀ-ÿ_0-9]*'
    t.type = palavras_reservadas.get(t.value, 'IDENTIFICADOR')
    return t


# conta '}' e coloca o numero da linha em uma lista
def t_FECHA_CHAVES_SOLO(t):
    r'\}'
    global FECHA_CHAVES_SOLO
    # FECHA_CHAVES += 1
    FECHA_CHAVES_SOLO.append(t.lineno)


# expressão regular para leitura de números ponto flutuante
def t_FLUTUANTE(t):
    # r'[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?')
    # r'\d+\. | \d+[eE][-+]\d+')
    r"[-+]?\d*\.\d+"
    t.value = float(t.value)
    return t


# expressão regular para leitura de números naturais
def t_INTEIRO(t):
    r'\d+'
    t.value = int(t.value)
    return t


# contador de linhas
def t_NOVA_LINHA(t):
    r'\n+'
    t.lexer.lineno += len(t.value)


# se encontrar algum caractere inválido que não foi definido exibe mensagem de erro
def t_error(t):
    # print("Caractere invalido '%s' linha %s" %(t.value[0], t.lineno))
    CARACTERES_INVALIDOS.append((t.value[0], t.lineno))
    t.lexer.skip(1)


# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ PARSER YACC ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

# classe arvore
from nani import Tree

# define a precedência dos operadores aritméticos
precedence = (
    ('left', 'IGUAL', 'MAIOR', 'MENOR', 'MENOR_IGUAL', 'MAIOR_IGUAL'),
    ('left', 'MAIS', 'MENOS'),
    ('left', 'MULTIPLICA', 'DIVIDIDO')
)


def p_programa(p):
    'programa : lista_declaracoes'
    p[0] = Tree('programa', [p[1]])


def p_lista_declaracoes(p):
    '''lista_declaracoes : lista_declaracoes declaracao
                         | declaracao'''
    if len(p) == 3:
        p[0] = Tree('lista_declaracoes', [p[1], p[2]])
    else:
        p[0] = Tree('lista_declaracoes', [p[1]])


def p_declaracao(p):
    '''declaracao : declaracao_variaveis
                  | inicializacao_variaveis
                  | declaracao_funcao'''
    p[0] = Tree('declaracao', [p[1]])


def p_declaracao_variaveis(p):
    'declaracao_variaveis : tipo DOIS_PONTOS lista_variaveis'
    p[0] = Tree('declaracao_variaveis', [p[1], p[3]])


def p_inicializacao_variaveis(p):
    'inicializacao_variaveis : atribuicao'
    p[0] = Tree('inicializacao_variaveis', [p[1]])


def p_lista_variaveis(p):
    '''lista_variaveis : lista_variaveis VIRGULA var
                       | var'''
    if len(p) == 4:
        p[0] = Tree('lista_variaveis', [p[1], p[3]])
    else:
        p[0] = Tree('lista_variaveis', [p[1]])


def p_var(p):
    '''var : IDENTIFICADOR
           | IDENTIFICADOR indice'''
    if len(p) == 3:
        p[0] = Tree('var', [p[2]], p[1])
    else:
        p[0] = Tree('var', [], p[1])


def p_indice(p):
    '''indice : indice ABRE_COLCHETES expressao FECHA_COLCHETES
              | ABRE_COLCHETES expressao FECHA_COLCHETES'''
    if len(p) == 5:
        p[0] = Tree('indice', [p[1], p[3]])
    else:
        p[0] = Tree('indice', [p[2]])


def p_tipo(p):
    '''tipo : TIPO_INTEIRO
            | TIPO_FLUTUANTE'''
    p[0] = Tree('tipo', [], p[1])


def p_declaracao_funcao(p):
    '''declaracao_funcao : tipo cabecalho
                         | cabecalho'''
    if len(p) == 3:
        p[0] = Tree('declaracao_funcao', [p[1], p[2]])
    else:
        p[0] = Tree('declaracao_funcao', [p[1]])


def p_cabecalho(p):
    'cabecalho : IDENTIFICADOR ABRE_PARENTESES lista_parametros FECHA_PARENTESES corpo FIM'
    p[0] = Tree('cabecalho', [p[3], p[5]], p[1])


def p_lista_parametros(p):
    '''lista_parametros : lista_parametros VIRGULA parametro
                         | parametro
                         | vazio'''
    if len(p) == 4:
        p[0] = Tree('lista_parametros', [p[1], p[3]])
    else:
        p[0] = Tree('lista_parametros', [p[1]])


def p_parametro(p):
    '''parametro : tipo DOIS_PONTOS IDENTIFICADOR
                 | parametro ABRE_COLCHETES FECHA_COLCHETES'''
    if p[2] == ':':
        p[0] = Tree('parametro', [p[1]], p[3])
    else:
        p[0] = Tree('parametro', [p[1]])


def p_corpo(p):
    '''corpo : corpo acao
             | vazio'''
    if len(p) == 3:
        p[0] = Tree('corpo', [p[1], p[2]])
    else:
        p[0] = Tree('corpo', [p[1]])


def p_acao(p):
    '''acao : expressao
            | declaracao_variaveis
            | se
            | repita
            | leia
            | escreva
            | retorna'''
    # | erro'''
    p[0] = Tree('acao', [p[1]])


def p_se(p):
    '''se : SE expressao ENTAO corpo FIM
          | SE expressao ENTAO corpo SENAO corpo FIM'''
    if len(p) == 6:
        p[0] = Tree('se', [p[2], p[4]])
    else:
        p[0] = Tree('se', [p[2], p[4], p[6]])


def p_repita(p):
    'repita : REPITA corpo ATE expressao'
    p[0] = Tree('repita', [p[2], p[4]])


def p_atribuicao(p):
    'atribuicao : var ATRIBUIR expressao'
    p[0] = Tree('atribuicao', [p[1], p[3]])


def p_leia(p):
    'leia : LEIA ABRE_PARENTESES var FECHA_PARENTESES'
    p[0] = Tree('leia', [p[3]])


def p_escreva(p):
    '''escreva : ESCREVA ABRE_PARENTESES expressao FECHA_PARENTESES'''
    p[0] = Tree('escreva', [p[3]])


def p_retorna(p):
    'retorna : RETORNA ABRE_PARENTESES expressao FECHA_PARENTESES'
    p[0] = Tree('retorna', [p[3]])


def p_expressao(p):
    '''expressao : expressao_logica
                 | atribuicao'''
    p[0] = Tree('expressao', [p[1]])


def p_expressao_logica(p):
    '''expressao_logica : expressao_simples
                        | expressao_logica operador_logico expressao_simples'''
    if len(p) == 2:
        p[0] = Tree('expressao_logica', [p[1]])
    else:
        p[0] = Tree('expressao_logica', [p[1], p[2], p[3]])


def p_expressao_simples(p):
    '''expressao_simples : expressao_aditiva
                         | expressao_simples operador_relacional expressao_aditiva'''
    if len(p) == 2:
        p[0] = Tree('expressao_simples', [p[1]])
    else:
        p[0] = Tree('expressao_simples', [p[1], p[2], p[3]])


def p_expressao_aditiva(p):
    '''expressao_aditiva : expressao_multiplicativa
                         | expressao_aditiva operador_soma expressao_multiplicativa'''
    if len(p) == 2:
        p[0] = Tree('expressao_aditiva', [p[1]])
    else:
        p[0] = Tree('expressao_aditiva', [p[1], p[2], p[3]])


def p_expressao_multiplicativa(p):
    '''expressao_multiplicativa : expressao_unaria
                                | expressao_multiplicativa operador_multiplicacao expressao_unaria'''
    if len(p) == 2:
        p[0] = Tree('expressao_multiplicativa', [p[1]])
    else:
        p[0] = Tree('expressao_multiplicativa', [p[1], p[2], p[3]])


def p_expressao_unaria(p):
    '''expressao_unaria : fator
                        | operador_soma fator'''
    # | operador_negacao fator'''
    if len(p) == 2:
        p[0] = Tree('expressao_unaria', [p[1]])
    else:
        p[0] = Tree('expressao_unaria', [p[1], p[2]])


def p_operador_relacinal(p):
    '''operador_relacional : MENOR
                           | MAIOR
                           | IGUAL
                           | DIFERENTE
                           | MENOR_IGUAL
                           | MAIOR_IGUAL'''
    p[0] = Tree('operador_relacional', [], p[1])


def p_operador_soma(p):
    '''operador_soma : MAIS
                     | MENOS'''
    p[0] = Tree('operador_soma', [], p[1])


def p_operador_logico(p):
    '''operador_logico : E_LOGICO
                       | OU_LOGICO'''
    p[0] = Tree('operador_logico', [], p[1])


def p_operador_multiplicacao(p):
    '''operador_multiplicacao : MULTIPLICA
                              | DIVIDIDO'''
    p[0] = Tree('operador_multiplicacao', [], p[1])


def p_fator(p):
    '''fator : ABRE_PARENTESES expressao FECHA_PARENTESES
             | var
             | chamada_funcao
             | numero'''
    if len(p) == 2:
        p[0] = Tree('fator', [p[1]])
    else:
        p[0] = Tree('fator', [p[2]])


def p_numero(p):
    '''numero : INTEIRO
              | FLUTUANTE'''
    p[0] = Tree('numero', [], p[1])


def p_chamada_funcao(p):
    'chamada_funcao : IDENTIFICADOR ABRE_PARENTESES lista_argumentos FECHA_PARENTESES'
    p[0] = Tree('chamada_funcao', [p[3]], p[1])


def p_lista_argumentos(p):
    '''lista_argumentos : lista_argumentos VIRGULA expressao
                        | expressao
                        | vazio'''
    if len(p) == 2:
        p[0] = Tree('lista_argumentos', [p[1]])
    else:
        p[0] = Tree('lista_argumentos', [p[1], p[3]])


def p_vazio(p):
    'vazio : '
    p[0] = Tree("vazio")
    pass


# ~~~~~~~~~~ alguns tratamentos de erro simples ~~~~~~~~~~~~~~~~~~~

def p_error(p):
    global ERRO_SINTATICO
    ERRO_SINTATICO = True
    if p:
        print('Erro sintatico: %s na linha %d' % (p.value, p.lineno))
    else:
        print('Esta faltando um "fim"')


def p_retorna_error(p):
    'retorna : RETORNA ABRE_PARENTESES error FECHA_PARENTESES'
    print("Função retorna não está recebendo nenhum argumento")


def p_declaracao_variaveis_error(p):
    'declaracao_variaveis : error DOIS_PONTOS lista_variaveis'
    print("Dica: possível erro na declaração de variável")


def p_indice_error(p):
    '''indice : indice ABRE_COLCHETES error FECHA_COLCHETES
          | ABRE_COLCHETES error FECHA_COLCHETES'''
    print("Dica: possível erro no índice entre colchetes")


def p_declaracao_cabecalho_error(p):
    'cabecalho : IDENTIFICADOR ABRE_PARENTESES lista_parametros FECHA_PARENTESES error FIM'
    print("Dica: possível erro no cabeçalho da função")


def p_atribuicao_error(p):
    'atribuicao : error ATRIBUIR expressao'
    print("Dica: possível erro na atribuição")


def p_leia_error(p):
    'leia : LEIA ABRE_PARENTESES error FECHA_PARENTESES'
    print("Função leia não está recebendo nenhum argumento")


def p_escreva_error(p):
    '''escreva : ESCREVA ABRE_PARENTESES error FECHA_PARENTESES'''
    print("Função escreva não está recebendo nenhum argumento")


# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ FIM PARSER YACC ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

# função recursiva para percorrer a árvore gerada e colocar no padrão aceito pela biblioteca anytree
def inorderTraversal2(root, pai=None):
    if root:
        temp = Node(root.type, parent=pai)
        if (root.leaf):
            Node(root.leaf, parent=temp)

        for filho in root.children:
            inorderTraversal2(filho, temp)

        return temp


# função recursiva para percorrer a árvore gerada e colocar no padrão aceito pela biblioteca graphviz
count = 0  # contador para modificar o id e gerar nós com mesmo nome sem bugar a árvore

# variavel para controle sem execução
semantic_error = False

def inorderTraversal3(root, pai=None):
    global dot, count
    if root:
        count += 1
        id = str(root.type) + str(count)

        dot.node(id, str(root.type))
        if pai:
            dot.edge(pai, id)
        if (root.leaf):
            count += 1
            id_leaf = str(root.leaf) + str(count)
            dot.node(id_leaf, str(root.leaf))
            dot.edge(id, id_leaf)

        for filho in root.children:
            inorderTraversal3(filho, id)

        return 0


# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ analisador semântico ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
class Linha():
    def __init__(self, nome, tipo, foiusada=False, tamanho1d=None, tamanho2d=None, linhaCodigo=None, qtdParam=None,
                 ehFunc=None, foiInic=None, valor=None):
        self.nome = nome
        self.tipo = tipo
        self.foiusada = foiusada
        self.tamanho1d = tamanho1d
        self.tamanho2d = tamanho2d
        self.linhaCodigo = linhaCodigo
        self.qtdParam = qtdParam
        self.ehFunc = ehFunc
        self.foiInic = foiInic
        self.valor = valor


class Table():
    def __init__(self, pai=None, filhos=None, nome=None):
        self.linhas = []
        if nome:
            self.nome = nome
        else:
            self.nome = "sem nome"
        if pai:
            self.pai = pai
        else:
            self.pai = None

        if filhos:
            self.filhos = filhos
        else:
            self.filhos = []

    def addLinha(self, nome, tipo, foiusada=None, tamanho1d=None, tamanho2d=None, linhaCodigo=None, qtdParam=None,
                 ehFunc=None, foiInic=None, valor=None):
        self.linhas.append(
            Linha(nome, tipo, foiusada, tamanho1d, tamanho2d, linhaCodigo, qtdParam, ehFunc, foiInic, valor))

    def deletLinhaByNome(self, nome):
        for i, row in enumerate(self.linhas):
            if nome == row.nome:
                del self.linhas[i]

    def addFilho(self, crianca):
        self.filhos.append(crianca)

    def foiDeclaradoEmEscopoValido(self, nome, paiArg=None):
        if paiArg:
            for row in paiArg.linhas:
                if row.nome == nome:
                    return True
            if paiArg.pai:
                return self.foiDeclaradoEmEscopoValido(nome, paiArg.pai)
        else:
            for row in self.linhas:
                if row.nome == nome:
                    return True
            if self.pai:
                return self.foiDeclaradoEmEscopoValido(nome, self.pai)

    def atualizafoiusada(self, nome, paiArg=None):
        if paiArg:
            for row in paiArg.linhas:
                if row.nome == nome:
                    row.foiusada = True
            if paiArg.pai:
                return self.atualizafoiusada(nome, paiArg.pai)
        else:
            for row in self.linhas:
                if row.nome == nome:
                    row.foiusada = True
            if self.pai:
                return self.atualizafoiusada(nome, self.pai)

    def atualizafoiinic(self, nome, paiArg=None):
        if paiArg:
            for row in paiArg.linhas:
                if row.nome == nome:
                    row.foiInic = True
            if paiArg.pai:
                return self.atualizafoiinic(nome, paiArg.pai)
        else:
            for row in self.linhas:
                if row.nome == nome:
                    row.foiInic = True
            if self.pai:
                return self.atualizafoiinic(nome, self.pai)

    def exibe(self):
        for row in self.linhas:
            print("Nome: ", row.nome, "|   Tipo: ", row.tipo, "|    FoiUsada: ", row.foiusada, "|    EhFunc: ",
                  row.ehFunc, "|    FoiInic: ", row.foiInic)

    def printaArvore(self, node=None):
        print("\n----------------------")
        if node == None:
            print("Nome Tabela: ", self.nome)
            self.exibe()
            print("----------------------\n")
            for son in self.filhos:
                self.printaArvore(son)
        if node:
            print("Nome Tabela: ", node.nome)
            node.exibe()
            print("----------------------")
            for son in node.filhos:
                self.printaArvore(son)

    def verificaVariaveisNaoUtilizadas(self, root=None):
        if root == None:
            for r in self.linhas:
                if ((r.foiusada == None) & (r.ehFunc == None)):
                    print("[AVISO]: Variavel '", r.nome, "' declarada mas não utilizada.")
                elif ((r.foiusada == None) & (r.ehFunc == True)):
                    print("[AVISO]: Função '", r.nome, "' declarada mas não utilizada.")
            for filho in self.filhos:
                filho.verificaVariaveisNaoUtilizadas(filho)
        if root:
            for r in root.linhas:
                if ((r.foiusada == None) & (r.ehFunc == None)):
                    print("[AVISO]: Variavel '", r.nome, "' declarada mas não utilizada.")
                elif ((r.foiusada == None) & (r.ehFunc == True)):
                    print("[AVISO]: Função '", r.nome, "' declarada mas não utilizada.")
            for filho in root.filhos:
                filho.verificaVariaveisNaoUtilizadas(filho)

    def verificaVariaveisNaoInicializadas(self, leaf=None, paiArg=None):
        if paiArg:
            for row in paiArg.linhas:
                if row.nome == leaf:
                    if not row.foiInic and (not row.ehFunc or row.ehFunc == ''):
                        print("[AVISO]: Variavel '", row.nome, "' declarada mas não inicializada.")
                    return row
            if paiArg.pai:
                return self.verificaVariaveisNaoInicializadas(leaf, paiArg.pai)
        else:
            for row in self.linhas:
                if row.nome == leaf:
                    if not row.foiInic and (not row.ehFunc or row.ehFunc == ''):
                        print("[AVISO]: Variavel '", row.nome, "' declarada mas não inicializada.")
                    return row
            if self.pai:
                return self.verificaVariaveisNaoInicializadas(leaf, self.pai)

    def procuraVarDeclaradaEMudaTipo(self, nome, tipo, paiArg=None):
        if paiArg:
            for row in paiArg.linhas:
                if row.nome == nome:
                    row.tipo = tipo
            if paiArg.pai:
                return self.procuraVarDeclaradaEMudaTipo(nome, tipo, paiArg.pai)
        else:
            for row in self.linhas:
                if row.nome == nome:
                    row.tipo = tipo
            if self.pai:
                return self.procuraVarDeclaradaEMudaTipo(nome, tipo, self.pai)

    def procuraPelaMain(self):
        if 'principal' not in [i.nome for i in self.linhas]:
            print("[ERRO]: Função principal não foi declarada")
            semantic_error = True


tabela_raiz = Table(nome="global")
guardaTipo = ""


def insereVariavelNaTabela(root, tabela_imutavel):
    global guardaTipo
    if root:
        if guardaTipo == None:
            guardaTipo = ""
        if root.leaf:
            if root.type == "tipo":
                guardaTipo = root.leaf
            if root.type == "var":
                if len(root.children) >= 1:
                    numb = pegaFolhaComPaiNumero(root)
                    if isinstance(numb, float):
                        print("[ERRO]: Indice de array '", root.leaf, "' não inteiro")
                        semantic_error = True
                        tabela_imutavel.addLinha(root.leaf, "inteiro", '', numb)
                    else:
                        tabela_imutavel.addLinha(root.leaf, "inteiro", '', numb)
                elif tabela_imutavel.foiDeclaradoEmEscopoValido(root.leaf):
                    print("[AVISO]: Variavel '", root.leaf, "' já declarada anteriormente")
                    tabela_imutavel.procuraVarDeclaradaEMudaTipo(root.leaf, guardaTipo)

                else:
                    tabela_imutavel.addLinha(root.leaf, guardaTipo)
        for fi in root.children:
            insereVariavelNaTabela(fi, tabela_imutavel)


# para fazer verificação de atribuição de tipos distintos
# retorna o nome do lado esquerdo da atribuiçao ex: a:=10 (retorna a)
def pegaFolhaComPaiVar(root):
    if root:
        if root.leaf:
            if root.type == "var":
                return root.leaf
        for fi in root.children:
            return pegaFolhaComPaiVar(fi)


def pegaFolhaComPaiNumero(root):
    if root:
        if root.leaf != None:
            # print(root.__dict__)
            if root.type == "numero":
                return root.leaf
        for fi in root.children:
            return pegaFolhaComPaiNumero(fi)


def pegaLadoDireitoAtribuicao(root):
    if root:
        if root.leaf != None:
            if root.type == "var":
                return root.leaf
            if root.type == "chamada_funcao":
                return root.leaf
            if root.type == "numero":
                return root.leaf
        x = []
        for filho in root.children:
            x.append(pegaLadoDireitoAtribuicao(filho))
        cv = list(filter(lambda n: n!=None, x))
        # print(cv,x)
        if len(cv) > 0:
            # print(cv[0])
            return cv[0]


# pega o tipo da variavel na tabela ja montada
def pegaTipoByNomeIterative(nome, pegaValor=None):
    global tabela_raiz
    vetor = []
    atual = tabela_raiz
    if pegaValor == None:
        for r in atual.linhas:
            if r.nome == nome:
                return r.tipo
        while (True):
            for child in atual.filhos:
                # child.exibe()
                if child:
                    for row in child.linhas:
                        if row.nome == nome:
                            return row.tipo
                    vetor.append(child)
            if len(vetor) == 0: break
            atual = vetor.pop(0)

    if pegaValor != None:
        for r in atual.linhas:
            if r.nome == nome:
                return r.tipo
        while (True):
            for child in atual.filhos:
                # child.exibe()
                if child:
                    for row in child.linhas:
                        if row.nome == nome:
                            return row.tipo
                    vetor.append(child)
            if len(vetor) == 0: break
            atual = vetor.pop(0)


# pega o tipo da variável/função pelo nome
# função recursiva
def pegaTipoVarNome(nome, root):
    if root:
        # root.exibe()
        for r in root.linhas:
            if r.nome == nome:
                return r.tipo
        x = []
        for f in root.filhos:
            x.append(pegaTipoVarNome(nome, f))
        if 'inteiro' in x:
            return 'inteiro'
        elif 'flutuante' in x:
            return 'flutuante'
        else:
            return 'vazio'


def pegaTipoDoRetornaIterativo(root):
    vetor = []
    atual = root
    if root.type == "retorna":
        if pegaFolhaComPaiVar(child):
            return pegaTipoByNomeIterative(pegaFolhaComPaiVar(child))
        elif isinstance(pegaFolhaComPaiNumero(child), (int, float, complex)):
            if isinstance(pegaFolhaComPaiNumero(child), int):
                return "inteiro"
            if isinstance(pegaFolhaComPaiNumero(child), float):
                return "flutuante"
    while (True):
        for child in atual.children:
            if child.type == "retorna":
                # print(root.children[0].__dict__)
                if pegaFolhaComPaiVar(child):
                    return pegaTipoByNomeIterative(pegaFolhaComPaiVar(child))
                elif isinstance(pegaFolhaComPaiNumero(child), (int, float, complex)):
                    # print(pegaFolhaComPaiNumero(child))
                    if isinstance(pegaFolhaComPaiNumero(child), int):
                        return "inteiro"
                    if isinstance(pegaFolhaComPaiNumero(child), float):
                        return "flutuante"

            vetor.append(child)
        if len(vetor) == 0: break
        atual = vetor.pop(0)


# passa o nome da func e retorna a qtdParam
def pegaqtdParamNaTabelaByNome(nome):
    global tabela_raiz
    vetor = []
    atual = tabela_raiz
    for r in atual.linhas:
        if r.nome == nome:
            return r.qtdParam
    while (True):
        for child in atual.filhos:
            if child:
                for row in child.linhas:
                    if row.nome == nome:
                        # print("entrei aqui")
                        return row.qtdParam
                vetor.append(child)
        if len(vetor) == 0: break
        atual = vetor.pop(0)
    return 0


# retorna a quantidade de parametros que estão definidos na declaracao de funcao
def pegaQuantidadeParametrosFuncao(root):
    vetor = []
    atual = root
    cont = 0
    while (True):
        for child in atual.children:
            if child.type == "parametro":
                cont = cont + 1

            vetor.append(child)
        if len(vetor) == 0: break
        atual = vetor.pop(0)
    return cont


# retorna a quantidade de parametros que foram passados em uma chamada de funcao
def pegaQuantidadeParametrosChamadaFuncao(root):
    vetor = []
    atual = root
    cont = 0
    while (True):
        for child in atual.children:
            if len(child.children) > 0:
                if child.type == "fator":
                    cont = cont + 1
                    continue
                vetor.append(child)
        if len(vetor) == 0: break
        atual = vetor.pop(0)
    return cont


# função chamada após a geração das tabelas para verificar se o tipo do retorna está certo
def verificaTipoRetorna(root, tabela=None):
    global tabela_raiz
    if root:
        for f in root.children:
            if f.type == "declaracao_funcao":
                if f.children[0].type == "tipo":
                    if f.children[0].leaf != pegaTipoDoRetornaIterativo(f):
                        if pegaTipoDoRetornaIterativo(f) == None:
                            print("[ERRO]: Função '", f.children[1].leaf, "' deveria retornar ",
                                  f.children[0].leaf, ", mas retorna vazio")
                            semantic_error = True
                        else:
                            print("[ERRO]: Função '", f.children[1].leaf, "' deveria retornar ",
                                  f.children[0].leaf, ", mas retorna ", pegaTipoDoRetornaIterativo(f))
                            semantic_error = True

                elif pegaTipoDoRetornaIterativo(f) != None:
                    print("[ERRO]: Função '", f.children[0].leaf, "' deveria retornar vazio, mas retorna",
                          pegaTipoDoRetornaIterativo(f))
                    semantic_error = True

            verificaTipoRetorna(f)


def percorreDeclaracaoFuncaoEAdicionaParametroNaTabela(root, tabela):
    vetor = []
    atual = root
    while (True):
        for child in atual.children:
            if child.type == "parametro":
                nome = child.leaf
                tipo = child.children[0].leaf
                tabela.addLinha(nome, tipo, None, '', '', '', '', True, foiInic=True)

            vetor.append(child)
        if len(vetor) == 0: break
        atual = vetor.pop(0)


def recomeco(root, tabela=None, pai=None):
    global tabela_raiz, semantic_error
    if root:
        temp = False
        f = root
        if f.type == "var" and not pai:
            if tabela != None:
                tabela.atualizafoiusada(f.leaf)
            else:
                tabela_raiz.atualizafoiusada(f.leaf)

            if tabela:
                # print("oi")
                tabela.verificaVariaveisNaoInicializadas(leaf=f.leaf)
            else:
                tabela_raiz.verificaVariaveisNaoInicializadas(leaf=f.leaf)

        for f in root.children:
            if f.type == "leia":
                tabela.atualizafoiinic(f.children[0].leaf)

            if f.type == "declaracao_funcao":
                if len(f.children) > 1:
                    new_table = Table(tabela_raiz, nome=f.children[1].leaf)
                    tabela_raiz.addFilho(new_table)
                else:
                    new_table = Table(tabela_raiz, nome=f.children[0].leaf)
                    tabela_raiz.addFilho(new_table)

                qtdParam = pegaQuantidadeParametrosFuncao(f)
                # significa que tem argumentos pra por na tabela
                if qtdParam > 0:
                    percorreDeclaracaoFuncaoEAdicionaParametroNaTabela(f, new_table)

                # se for menor que 1 significa que nao tem tipo a funcao então manda vazio
                if len(f.children) > 1:
                    if f.children[1].leaf == "principal":
                        tabela_raiz.addLinha(f.children[1].leaf, f.children[0].leaf, '', '', '', '', qtdParam, True)
                    else:
                        tabela_raiz.addLinha(f.children[1].leaf, f.children[0].leaf, None, '', '', '', qtdParam, True)
                else:
                    if f.children[0].leaf == "principal":
                        tabela_raiz.addLinha(f.children[0].leaf, "vazio", '', '', '', '', qtdParam, True),
                    else:
                        tabela_raiz.addLinha(f.children[0].leaf, "vazio", None, '', '', '', qtdParam, True),

                temp = True
            if f.type == "se":
                new_table = Table(tabela, nome="se")
                tabela.addFilho(new_table)
                temp = True
            if f.type == "repita":
                new_table = Table(tabela, nome="repita")
                tabela.addFilho(new_table)
                temp = True

            if f.type == "retorna":
                if pegaFolhaComPaiVar(f):
                    if not tabela.foiDeclaradoEmEscopoValido(pegaFolhaComPaiVar(f)):
                        print("[ERRO]: Variavel '", pegaFolhaComPaiVar(f), "' nao foi declarada")
                        semantic_error = True

            if f.type == "chamada_funcao":
                if tabela != None:
                    if f.leaf == "principal":
                        print("[AVISO]: Chamada recursiva para a função 'principal'")
                    if not tabela.foiDeclaradoEmEscopoValido(f.leaf):
                        print("[ERRO]: Chamada a função '", f.leaf, "' que não foi declarada")
                        semantic_error = True

                    if pegaQuantidadeParametrosChamadaFuncao(f) < pegaqtdParamNaTabelaByNome(f.leaf):
                        print("[ERRO]: Chamada a função '", f.leaf, "' com número de parâmetros menor que o declarado")
                        semantic_error = True
                    # print(pegaQuantidadeParametrosChamadaFuncao(f))
                    # print(pegaqtdParamNaTabelaByNome(f))
                    # if pegaQuantidadeParametrosChamadaFuncao(f) > pegaqtdParamNaTabelaByNome(f.leaf):
                        # print("[ERRO]: Chamada a função '", f.leaf, "' com número de parâmetros maior que o declarado")
                        # semantic_error = True

                    tabela.atualizafoiusada(f.leaf)

            if f.type == "declaracao_variaveis":
                pai = True
                if root.type == "acao":
                    insereVariavelNaTabela(f, tabela)
                else:
                    insereVariavelNaTabela(f, tabela_raiz)
            pai2 = False

            if f.type == "atribuicao":
                if tabela != None:
                    pai = True
                    tabela.atualizafoiinic(f.children[0].leaf)
                    # descomente esta linha para atribuiçao começar a contar como variavel utilizada
                    # tabela.atualizafoiusada(f.children[0].leaf)

                    # se for igual numero
                    y = pegaLadoDireitoAtribuicao(f.children[1])
                    # só funciona para alguns casos específicos (arrumar depois)
                    # print(pegaLadoDireitoAtribuicao(f.children[1]))
                    # if isinstance(y, str):
                        # if f.children[0].leaf == y:
                            # print("[AVISO]: Variavel '", y, "' declarada mas não inicializada.")
                        # else:
                            # x = tabela_raiz.verificaVariaveisNaoInicializadas(leaf=y)
                    # print(x.__dict__)
                    if (isinstance(pegaLadoDireitoAtribuicao(f.children[1]), (int, float))):
                        if isinstance(pegaLadoDireitoAtribuicao(f.children[1]), int):
                            if pegaTipoVarNome(pegaFolhaComPaiVar(f), tabela_raiz) != "inteiro":
                                print("[AVISO]: Atribuição de tipos distintos '", pegaFolhaComPaiVar(f), "' ",
                                      pegaTipoVarNome(pegaFolhaComPaiVar(f), tabela_raiz), "'",
                                      pegaLadoDireitoAtribuicao(f.children[1]), "' inteiro")
                        elif isinstance(pegaLadoDireitoAtribuicao(f.children[1]), float):
                            if pegaTipoVarNome(pegaFolhaComPaiVar(f), tabela_raiz) != "flutuante":
                                print("[AVISO]: Atribuição de tipos distintos '", pegaFolhaComPaiVar(f), "' ",
                                      pegaTipoVarNome(pegaFolhaComPaiVar(f), tabela_raiz), "'",
                                      pegaLadoDireitoAtribuicao(f.children[1]), "' flutuante")

                    # senao se for igual variavel/func
                    elif tabela.foiDeclaradoEmEscopoValido(pegaLadoDireitoAtribuicao(f.children[1])):
                        if pegaTipoVarNome(pegaFolhaComPaiVar(f), tabela_raiz) != pegaTipoVarNome(
                                pegaLadoDireitoAtribuicao(f.children[1]), tabela_raiz):
                            print("[AVISO]: Atribuição de tipos distintos '",
                                  pegaFolhaComPaiVar(f), "' ",
                                  pegaTipoVarNome(pegaFolhaComPaiVar(f), tabela_raiz),
                                  " e '", pegaLadoDireitoAtribuicao(f.children[1]),
                                  "' ", pegaTipoVarNome(pegaLadoDireitoAtribuicao(f.children[1]), tabela_raiz))
                        else:
                            tabela.atualizafoiusada(pegaLadoDireitoAtribuicao(f.children[1]))

                    elif not isinstance(pegaLadoDireitoAtribuicao(f.children[1]), (int, float, complex)):
                        print("[ERRO]: Variavel '", pegaLadoDireitoAtribuicao(f.children[1]), "' não declarada")
                        semantic_error = True
                    if tabela.foiDeclaradoEmEscopoValido(f.children[0].leaf) != True:
                        print("[ERRO]: Variavel", f.children[0].leaf, "nao foi declarada")
                        semantic_error = True
                else:
                    print("[ERRO]: Variavel", f.children[0].leaf, "nao foi declarada")
                    semantic_error = True

            if temp:
                recomeco(f, new_table, pai=pai)
            else:
                recomeco(f, tabela, pai=pai)


# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~  コード生成 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# percorre árvore sintática abstrata

# variavel para controle de erro sem execuçao



# classe pra gerar codigo

class KodoGen():
    def __init__(self, arvorinha):
        self.vars = []  # lista de variaveis
        self.funcoes = []  # lista de funcoes
        self.module = ir.Module('meu_modulo.bc')  # cria módulo
        self.fimbloco = ''
        self.retornodafunc = ''
        self.global_var = {}
        self.local_var = {}
        self.dicionario_var = {}
        self.func_name = None
        self.count = 1
        self.retorna = False
        self.traversalAST(arvorinha)
        arquivo = open('meu_modulo.ll', 'w')
        arquivo.write(str(self.module))
        arquivo.close()
        print(self.module)

    def trataVarGlob(self, root):
        # print(root.type)
        array_nomes = []
        array_nos_vetor = []  # lista com referencia de nós para variaveis q sao vetor
        for i in root.children[1].children:
            if len(i.children) > 0:
                array_nos_vetor.append(i)  # guarda no com nome e filho indice do vetor

        # print(array_nos_vetor[0].children[0].type)

        for f in root.children[1].children:
            if len(i.children) == 0:
                array_nomes.append(f.type)

        var_tipo = root.children[0].leaf

        # print(var_tipo)
        if var_tipo == "inteiro":
            for nome in array_nomes:
                g = ir.GlobalVariable(self.module, ir.IntType(32), nome)  # Variável inteira global
                g.initializer = ir.Constant(ir.IntType(32), 0)  # Inicializa a variavel g
                g.linkage = "common"  # Linkage = common
                g.align = 4  # Define o alinhamento em 4
                self.global_var[nome] = g
                self.vars.append(nome)

            if len(array_nos_vetor) > 0:  # se for vetor de inteiro
                for w in array_nos_vetor:
                    tempRef = ir.GlobalVariable(self.module,
                                                ir.ArrayType(element=ir.IntType(32), count=int(w.children[0].type)),
                                                w.type)
                    tempRef.initializer = ir.Constant(ir.ArrayType(element=ir.IntType(32), count=int(w.children[0].type)), None)
                    tempRef.linkage = "common"
                    tempRef.align = 4
                    self.global_var[w.type] = tempRef
        elif var_tipo == "flutuante":
            for nome in array_nomes:
                h = ir.GlobalVariable(self.module, ir.DoubleType(), nome)  # Variável float global h
                h.initializer = ir.Constant(ir.DoubleType(), 0.0)  # Inicializa a variavel h
                h.linkage = "common"  # Linkage = common
                h.align = 4  # Define o alinhamento em 4
                self.global_var[nome] = h
                self.vars.append(nome)

            if len(array_nos_vetor) > 0:  # se for vetor de inteiro
                for w in array_nos_vetor:
                    tempRef = ir.GlobalVariable(self.module,
                                                ir.ArrayType(element=ir.DoubleType(), count=int(w.children[0].type)),
                                                w.type)
                    tempRef.initializer = ir.Constant(ir.ArrayType(element=ir.DoubleType(), count=int(w.children[0].type)), None)
                    tempRef.linkage = "common"
                    self.global_var[w.type] = tempRef

    # percorre corpo da funcao
    def traversalFunc(self, root, builder):
        if root:
            if self.retorna == True:
                return

            if root.type == "declaracao_variaveis":
                self.declaracaoVar(root, builder)
            if root.type == "atribuicao":
                self.atribuicao(root, builder)
            if root.type == "repita":
                return self.trataRepita(root, builder)
            if root.type == "chamada_funcao":
                self.trataFuncCall(root, builder)
            if root.type == "escreva":
                self.trataEscreva(root, builder)
            if root.type == "leia":
                self.trataLeia(root,builder)
            if root.type == "se":
                return self.trataSe(root, builder)
            if root.type == "retorna":
                self.montaRetorna(root, builder)

            for f in root.children:
                self.traversalFunc(f, builder)

    def pegaParametro(self, no):
        vetor = []
        atual = no
        lista = []
        # print("wtf")
        while (True):
            for child in atual.children:
                # print(child.type)
                if child.type == "parametro":
                    lista.append((child.leaf, child.children[0].leaf))

                vetor.append(child)
            if len(vetor) == 0: break
            atual = vetor.pop(0)
        # print(lista)
        return lista

    def trataDeclaraFunc(self, root):
        parametro = []
        nome = root.children[-1].leaf  # nome da func
        self.retorna = False
        tipo = None  # tipo da funcao pro controle do retorna

        if len(root.children) == 2:  # entao funcao tem tipo
            # se tiver parametros
            if len(root.children[1].children[1].children) > 0:  # parametros?
                # print(root.children[1].children[0].type)
                tupla_params = self.pegaParametro(root.children[1].children[0])
                # print(tupla_params)
                for i in tupla_params:
                    if i[1] == "inteiro":
                        parametro.append(ir.IntType(32))
                    elif i[1] == "flutuante":
                        parametro.append(ir.DoubleType())
            if root.children[0].leaf == "inteiro":
                tfunc = ir.FunctionType(ir.IntType(32), (parametro))
                tipo = ir.IntType(32)
            elif root.children[0].leaf == "flutuante":
                tfunc = ir.FunctionType(ir.DoubleType(), (parametro))  # cria retorno
                tipo = ir.DoubleType()

        else:  # senao se funcao nao tem tipo
            if len(root.children[0].children[1].children) > 0:  # parametros?
                tupla_params = self.pegaParametro(root.children[0].children[0])
                for i in tupla_params:
                    if i[1] == "inteiro":
                        parametro.append(ir.IntType(32))
                    elif i[1] == "flutuante":
                        parametro.append(ir.DoubleType())

            tfunc = ir.FunctionType(ir.VoidType(), (parametro))



        func = ir.Function(self.module, tfunc, name=nome)
        entryBlock = func.append_basic_block('inicio' + nome)
        builder = ir.IRBuilder(entryBlock)
        if tipo:
            self.retornodafunc = builder.alloca(tipo, name='ret')

        for arg, name in zip(func.args, [i[0] for i in tupla_params]):
            arg.name = name

        self.funcoes.append(func)

        self.func_name = func

        for i in func.args:
            x = builder.alloca(i.type, name=i.name)
            x.align = 4
            self.local_var[i.name] = x
            builder.store(i, x)

        endBasicBlock = func.append_basic_block('fim' + nome)
        self.fimbloco = endBasicBlock

        self.traversalFunc(root, builder)
        
        builder.branch(endBasicBlock)

        builder.position_at_end(endBasicBlock)

        if len(root.children) != 2:
            builder.ret_void()
        else:
            x = builder.load(self.retornodafunc)

            builder.ret(x)


    # percorre arvore procurando por func e vars glob
    def traversalAST(self, root, pai=None):
        if root:
            # se pai é lista_declaracoes então variável é global
            if pai:
                if pai.type == "lista_declaracoes":
                    if root.type == "declaracao_variaveis":
                        self.trataVarGlob(root)
            if root.type == "declaracao_funcao":
                self.trataDeclaraFunc(root)
            # pass
            for f in root.children:
                self.traversalAST(f, root)

    def declaracaoVar(self, no, builder):

        list_nomes = []  # guarda nome das variaveis
        tipo_var = no.children[0].leaf
        array_nos_vetor = []
        for i in no.children[1].children:
            if len(i.children) > 0:
                array_nos_vetor.append(i)  # guarda no com nome e filho indice do vetor

        for nomes in no.children[1].children:
            if len(nomes.children) == 0:
                list_nomes.append(nomes)
        if tipo_var == "inteiro":
            if len(array_nos_vetor) > 0:
                for w in array_nos_vetor:
                    x = builder.alloca(ir.ArrayType(element=ir.IntType(32), count=int(w.children[0].type)), name=w.type)
                    x.align = 4
                    self.vars.append(x)
                    self.local_var[w.type] = x
            for i in list_nomes:
                x = builder.alloca(ir.IntType(32), name=i.type)
                x.align = 4
                self.vars.append(x)
                self.local_var[i.type] = x
        elif tipo_var == "flutuante":
            if len(array_nos_vetor) > 0:
                for w in array_nos_vetor:
                    x = builder.alloca(ir.ArrayType(element=ir.DoubleType(), count=int(w.children[0].type)), name=w.type)
                    x.align = 4
                    self.vars.append(x)
                    self.local_var[w.type] = x
            for i in list_nomes:
                x = builder.alloca(ir.DoubleType(), name=i.type)
                x.align = 4
                self.vars.append(x)
                self.local_var[i.type] = x

    def expressao(self, no, builder, pegaPtr=None):
        array = []
        nome = no.type
        if nome == "chamada_funcao":
            return self.trataFuncCall(no, builder)
        for f in no.children:
            array.append(self.expressao(f, builder))
        # print(array)
        if len(array) == 0 or (len(array) == 1 and isinstance(nome, str)):
            if isinstance(nome, str):

                x = None
                if nome in self.local_var.keys():
                    x = self.local_var[nome]
                if nome in self.global_var.keys():
                    x = self.global_var[nome]

                # tratamento de vetor
                if len(no.children) > 0:
                    indicedovet = no.children[0]
                    teste = self.expressao(indicedovet, builder)
                    zero = ir.Constant(ir.IntType(32), 0)

                    vet_ptr = builder.gep(x, [zero, teste], inbounds=True)

                    return builder.load(vet_ptr)
                if pegaPtr == None:
                    return builder.load(x)
                else:
                    return x
            else:  # se for numero
                if isinstance(nome, int):
                    return ir.Constant(ir.IntType(32), nome)
                elif isinstance(nome, float):
                    return ir.Constant(ir.DoubleType(), nome)
        elif len(array) == 2:  # se tem filhos
            if array[0].type != array[1].type:
                if str(array[0].type) == "double":
                    array[1] = builder.uitofp(array[1], array[0].type)
                    print(array[1])
                else:
                    array[0] = builder.uitofp(array[0], array[1].type)

            if nome == "+":
                print(array[0].type)
                if str(array[0].type) == "double" or str(array[1].type) == "double":
                    return builder.fadd(array[0], array[1], name="addFloat")
                else:
                    return builder.add(array[0], array[1], name="addInt")
            if nome == "-":
                return builder.sub(array[0], array[1], name="temp")
            if nome == "*":
                if str(array[0].type) == 'double':
                    return builder.fmul(array[0], array[1], name="temp")
                else:
                    return builder.mul(array[0], array[1], name="temp")
            if nome == "/":
                if str(array[0].type) == 'double':
                    return builder.fdiv(array[0], array[1], name="temp")
                else:
                    return builder.udiv(array[0], array[1], name="temp")
            if nome == "||":
                return builder.or_(array[0], array[1], name="temp")
            if nome == "&&":
                return builder.and_(array[0], array[1], name="temp")
            if nome in [">", "<", ">=", "<="]:
                return builder.icmp_signed(nome, array[0], array[1], name="temp")
            if nome == "<>":
                return builder.icmp_signed("!=", array[0], array[1], name="temp")
            if nome == "=":
                return builder.icmp_signed("==", array[0], array[1], name="temp")


        elif len(array) == 1:  # se for expressao unaria
            if nome == "+":
                return builder.add(ir.Constant(ir.IntType(32), 0), array[0], name="temp")
            if nome == "-":
                return builder.sub(ir.Constant(ir.IntType(32), 0), array[0], name="temp")
        raise ArithmeticError("nao foi implementado ainda: ", nome)

    def atribuicao(self, no, builder):
        nome_var = no.children[0].type
        tipo_var = pegaTipoByNomeIterative(nome_var)  # tipo da variavel q será atribuida
        x = None
        if nome_var in self.local_var.keys():
            x = self.local_var[nome_var]
        if nome_var in self.global_var.keys():
            x = self.global_var[nome_var]
        resultado = self.expressao(no.children[1], builder)
        # print(no.children[1].type)
        # self.dicionario_var[no.children[0].type] = no.children[1].type
        if len(no.children[0].children) > 0:
            print(no.children[0].children[0].type)
            # self.dicionario_var[no.children[0].children[0].type] = no.children[1].type
        if str(resultado.type) not in str(x.type):
            if str(x.type) == "i32*":
                resultado = builder.fptoui(resultado, ir.IntType(32))
            else:
                resultado = builder.uitofp(resultado, ir.DoubleType())

        if len(no.children[0].children) > 0:  # significa q é vetor
            indicedovet = no.children[0].children[0]
            teste = self.expressao(indicedovet, builder)
            zero = ir.Constant(ir.IntType(32), 0)
            # print(x)
            vet_ptr = builder.gep(x, [zero, zero], inbounds=True)
            resultadofinal = builder.gep(vet_ptr, [teste], inbounds=True)
            # print(vet_ptr)
            builder.store(resultado, resultadofinal)
        else:
            # print(no.children[1].type)
            # resultado = self.expressao(no.children[1], builder)
            builder.store(resultado, x)

    def montaRetorna(self, no, builder):
        self.retorna = True
        valor_retorna = self.expressao(no.children[0], builder)

        builder.store(valor_retorna, self.retornodafunc)
        # builder.branch(self.fimbloco)

    # builder.position_at_end(self.fimbloco)
    # novobloco_ret = self.func_name.append_basic_block('blocodoretorna')
    # builder.branch(novobloco_ret)
    # with builder.goto_block(novobloco_ret):
    # builder.ret(valor_retorna)
    # builder.position_at_start(novobloco_ret)

    def trataSe(self, no, builder):

        # novobloco_se = self.func_name.append_basic_block('se')
        # novobloco_senao = self.func_name.append_basic_block('senao')
        # novobloco_fim = self.func_name.append_basic_block('fim')

        a_cmp = self.expressao(no.children[0].children[0], builder)
        b_cmp = ir.Constant(ir.IntType(32), 0)
        cond = builder.icmp_signed("!=", a_cmp, b_cmp, name="comparacao")

        if len(no.children) == 2:
            with builder.if_then(cond):
                self.traversalFunc(no.children[1], builder)
        else:
            with builder.if_else(cond) as (then, otherwise):
                with then:
                    self.traversalFunc(no.children[1], builder)
                with otherwise:
                    self.traversalFunc(no.children[2], builder)


        # builder.cbranch(cond, novobloco_se, novobloco_senao)
        # builder.position_at_end(novobloco_se)
        # self.traversalFunc(no.children[1], builder)
        # if self.retorna == False:
        #     builder.branch(novobloco_fim)

        # builder.position_at_end(novobloco_senao)
        # if len(no.children) == 3:  # se tem senão
        #     # print("entrei", no.children[2].type)
        #     self.retorna = False
        #     self.traversalFunc(no.children[2], builder)
        # if self.retorna == False:
        #     builder.branch(novobloco_fim)

        # builder.position_at_end(novobloco_fim)

    def trataRepita(self, no, builder):
        bloco_condicao = self.func_name.append_basic_block('condicao_repita')
        bloco_repita = self.func_name.append_basic_block('bloco_repita')
        bloco_fim_do_repita = self.func_name.append_basic_block('bloco_fim_do_repita')
        
        x = builder.branch(bloco_repita)  # nao testa condicao por isso vai direto pro bloco do repita
        builder.position_at_end(bloco_repita)  # Position at the end of the basic block.
        self.traversalFunc(no.children[0], builder)  # manda o no = 'então'
        # if self.retorna == False:
        builder.branch(bloco_condicao)  # bloco condicao

        builder.position_at_end(bloco_condicao)  # Position at the end of the basic block.
        
        result = self.expressao(no.children[1].children[0], builder)  # manda o nó = 'condicao'
        
        b_cmp = ir.Constant(ir.IntType(32), 0)  # cria o 0 pra comparar
        cond = builder.icmp_signed("==", result, b_cmp,name="comparacao_repita")  # o self.expressao retorna o valor da comparacao
        builder.cbranch(cond, bloco_repita, bloco_fim_do_repita)  # salto de bloco condicional cbranch
        builder.position_at_end(bloco_fim_do_repita)  # position at the end of the basic block
        # if self.retorna == True:
        # builder.branch(self.fimbloco)

    def trataFuncCall(self, no, builder):
        nome_func = no.leaf  # nome da func
        lista = []
        # print("qq isso")
        # print(no.children[0].children[0].type)
        for i in no.children[0].children:

            lista.append(self.expressao(i, builder))
        guardaFunc = None
        for x in self.funcoes:
            if nome_func == x.name:
                guardaFunc = x
        for i,(parametroW, parametroR) in enumerate(zip(lista, guardaFunc.args)):
            if str(parametroW.type) not in str(parametroR.type):
                if "double" in str(parametroR.type):
                    x = builder.uitofp(parametroW, ir.DoubleType())
                    lista[i] = x
                elif "i32" in str(parametroR.type):
                    x = builder.fptoui(parametroW, ir.IntType(32))
                    lista[i] = x
        return builder.call(guardaFunc, lista)

    def trataEscreva(self, no, builder):
        retexpress = self.expressao(no.children[0], builder)
        print("ASDKASKD")
        argumento_escreva = retexpress
        print(argumento_escreva.type)
        tmp = None
        if 'i32' in str(argumento_escreva.type):
            tmp = "%d\n\0"
        elif 'double' in str(argumento_escreva.type):
            tmp = "%lf\n\0"

        ptr = ir.ArrayType(ir.IntType(8), len(tmp))
        # ptr = ir.DoubleType()
        self.count = self.count + 1
        varGlob = ir.GlobalVariable(self.module, ptr, "escreva" + str(self.count))
        varGlob.initializer = ir.Constant(ptr, bytearray(tmp, encoding="utf-8"))
        varGlob.global_constant = True
        lista_argumentos = [varGlob, argumento_escreva]
        lista_temp = []
        for i in lista_argumentos:
            lista_temp.append(i.type)

        func = ir.FunctionType(ir.IntType(32), (), var_arg=True)
        func_llvm = self.module.declare_intrinsic("printf", (), func)
        builder.call(func_llvm, lista_argumentos)

    def trataLeia(self, no, builder):
        retexpress = self.expressao(no.children[0], builder, pegaPtr=True)
        argumento_leia = retexpress

        tmp = None
        if 'i32' in str(argumento_leia.type):
            tmp = "%d\0"
        elif 'double' in str(argumento_leia.type):
            tmp = "%lf\0"
        ptr = ir.ArrayType(ir.IntType(8), len(tmp))
        self.count = self.count + 1
        varGlob = ir.GlobalVariable(self.module, ptr, "leia" + str(self.count))
        varGlob.initializer = ir.Constant(ptr, bytearray(tmp, encoding="utf-8"))
        varGlob.global_constant = True
        lista_argumentos = [varGlob, argumento_leia]
        lista_temp = []
        for i in lista_argumentos:
            lista_temp.append(i.type)
        func = ir.FunctionType(ir.IntType(32), (), var_arg=True)
        func_llvm = self.module.declare_intrinsic("scanf", (), func)
        builder.call(func_llvm, lista_argumentos)
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~  メインコード ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


# abre o arquivo e armazena o contéudo na variável data
f = open(sys.argv[1], "r", encoding="utf-8")
data = f.read()

# analisador léxico
lex.lex()
lex.input(data)
# log = logging.getLogger('ply')

# analisador sintático
parser = yacc.yacc(debug=True)

# cria a árvore do graphviz para gerar o pdf
dot = Digraph(comment='Arvore Sintatica')

# faz o parser do sysArg
parser_Args = argparse.ArgumentParser()
parser_Args.add_argument("file")
parser_Args.add_argument("-a", "--ast", help="Exibe a árvore sintática no terminal", action="store_true", default=False)
parser_Args.add_argument("-p", "--pdf", help="Gera um pdf da árvore sintática", action="store_true", default=False)
parser_Args.add_argument("-t", "--ts", help="Gera um pdf da árvore sintática", action="store_true", default=False)
parser_Args.add_argument("-g", "--gc", help="Geração de código", action="store_true", default=False)
parser_Args.add_argument("-r", "--run", help="Geração de código", action="store_true", default=False)

args = vars(parser_Args.parse_args())

result = parser.parse(data)
recomeco(result)

verificaTipoRetorna(result)  # só consigo fazer a verificação após ter a tabela de simbolo completa
tabela_raiz.procuraPelaMain()
tabela_raiz.verificaVariaveisNaoUtilizadas()
# x = result
# reduçao da arvore
x = arv_reduzida(result)

# percorre pra geracao de codigo


# código para printar arvore sintática, caso seja digitado o comando Tree
if (not ERRO_SINTATICO):
    # print("Análise sintática realizada com sucesso")
    if (args['ast']):
        # a = inorderTraversal2(result)
        a = inorderTraversal2(x)
        DotExporter(a).to_dotfile("arvore.dot")  # picture gera img
        for pre, _, node in RenderTree(a, style=DoubleStyle()):
            print("%s%s" % (pre, node.name))
    if (args['pdf']):
        inorderTraversal3(x)  # mudar pra result para nao podar
        dot.render('test-output/arvore', view=True)
    if (args['ts']):
        tabela_raiz.printaArvore()
    if (args['gc']):
        # print(semantic_error)
        if semantic_error: 
            exit(1)    
        oi = KodoGen(x)

    if (args['run']):
        call(['llvm-as', 'meu_modulo.ll', '-o', 'meu_modulo.bc'])
        call(['llc', 'meu_modulo.bc', '-o', 'meu_modulo.s', '--mtriple',
              'x86_64-pc-linux-gnu'])
        call(['gcc', 'meu_modulo.s', '-o', 'exec', '-no-pie'])
        call(['./exec'])
# exibição dos erros gerados pelo analisador léxico
lista = []
while True:
    tok = lex.token()
    if not tok: break
    lista.append((tok.type, str(tok.value)))
# parser.parse(tok)
if FECHA_CHAVES_SOLO or ABRE_CHAVES_LINHA:
    while FECHA_CHAVES_SOLO:
        print('Foi fechado \'}\', mas nao foi aberto! Linha:', FECHA_CHAVES_SOLO.pop())
    while ABRE_CHAVES_LINHA:
        print('Foi aberto \'{\', mas nao foi fechado! Linha:', ABRE_CHAVES_LINHA.pop())

elif CARACTERES_INVALIDOS:
    for i in range(len(CARACTERES_INVALIDOS)):
        print("Caractere Invalido: '%s', Linha: %s" % CARACTERES_INVALIDOS[i])

# exibe a lista de tokens gerada pelo analisador léxico, necessário comentar o yacc para ver a lista
else:
    for i in range(len(lista)):
        print(lista[i])
