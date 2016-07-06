# -*- coding: utf-8 -*-

from sage.all import * # importar tudo do sage

#def. pairing
def pairing(p1, p2):
	return (E2(p1).weil_pairing(E2(-p2[0], alpha*p2[1]), ZZ(r)))


def construirT(listaRaizes):
	x = var('x')
	t = 0
	t = prod((x - ri) for ri in listaRaizes)
	return P(t)

#constroi a prova
def construirProof():
	proof.append(Vmid * gv)
	proof.append(Wmid * gw)
	proof.append(Ymid * gy)
	proof.append(ZZ(h(ZZ(s))) * g)
	proof.append(ZZ(alfa_v) * Vmid * gv)
	proof.append(ZZ(alfa_w) * Wmid * gw)
	proof.append(ZZ(alfa_y) * Ymid * gy)
	proof.append((ZZ(beta) * Vmid * gv) + (ZZ(beta) * Wmid * gw) + (ZZ(beta) * Ymid * gy))

#constroi a evaluation key
def construirEK():
	for i in range(0,8):
		EK.append([])

	for i in range(1,nRaizes+1):
		EK[6].append(ZZ(s**i) * g)

	for k in Imid:
		EK[0].append(ZZ(V[k](ZZ(s))) * gv)
		EK[1].append(ZZ(W[k](ZZ(s))) * gw)
		EK[2].append(ZZ(Y[k](ZZ(s))) * gy)
		EK[3].append(ZZ(alfa_v) * ZZ(V[k](ZZ(s))) * gv)
		EK[4].append(ZZ(alfa_w) * ZZ(W[k](ZZ(s))) * gw)
		EK[5].append(ZZ(alfa_y) * ZZ(Y[k](ZZ(s))) * gy)
		EK[7].append((ZZ(beta) * ZZ(V[k](ZZ(s))) * gv) + (ZZ(beta) * ZZ(W[k](ZZ(s))) * gw) + (ZZ(beta) * ZZ(Y[k](ZZ(s))) * g))

#constroi a verification key
def construirVK():
	VK.append(g)
	VK.append(ZZ(alfa_v) * g)
	VK.append(ZZ(alfa_w) * g)
	VK.append(ZZ(alfa_y) * g)
	VK.append(ZZ(omga) * g)
	VK.append(ZZ(beta) * ZZ(omga) * g)
	VK.append(ZZ(t(ZZ(s))) * gy)

	aux = []
	for k in range(0,N):
		aux.append([ZZ(V[k](ZZ(s))) * gv,ZZ(W[k](ZZ(s))) * gw,ZZ(Y[k](ZZ(s))) * gy])
	VK.append(aux)


#ira construir V,W,Y
def construirConjPolinomios(ops,V,W,Y,nRaizes):
	contaRaiz = 0 #diz-nos qual gate de mutiplicacao (raiz) estamos
	contaOps = 0 # conta operaçoes de input e multiplicacao, indica em qual indice dos vetores V,W e Y os polinomios relativos a cada input e mutiplicacao devem ser colocados

	#
	for i in range(0,len(ops)):
		if ops[i].split(' ', 1)[0] == "input":
			###    Y
			aux = []
			for j in range (0,nRaizes):
				aux.append((j+1,0))

			Y[contaOps] = P.lagrange_polynomial(aux)
			###   fim Y	

			contaOps += 1

		elif ops[i].split(' ', 1)[0] == "mult":
			contaRaiz += 1 # diz em que gate mutiplicacao estamos,
			
			###   V
			aux = []
			indiceEsq = int(ops[i].split(' ', 3)[1])
			if ops[indiceEsq -1].split(' ', 1)[0] == "input":
				for j in range (0,nRaizes):
					if j+1 == contaRaiz:
						aux.append((contaRaiz,1))
					else:
						aux.append((j+1,0))
				V[indiceEsq - 1] = P.lagrange_polynomial(aux)
			elif ops[indiceEsq - 1].split(' ', 1)[0] == "mult":
				nAdds = int(ops[indiceEsq - 1].split(' ', 3)[3])# n de "add" antes desta mult		
				for j in range (0,nRaizes):
					if j+1 == contaRaiz:
						aux.append((contaRaiz,1))
					else:
						aux.append((j+1,0))
				V[indiceEsq - 1 - nAdds] = P.lagrange_polynomial(aux)
			elif ops[indiceEsq - 1].split(' ', 1)[0] == "add":
				stack = []
				nItems = 0

				stack.append(int(ops[indiceEsq - 1].split(' ', 2)[1]))
				stack.append(int(ops[indiceEsq - 1].split(' ', 2)[2]))
				nItems += 2

				while nItems > 0:
					k = stack[nItems-1] # k (elemento no topo da stack) é o indice do vetor ops que vamos analisar se é mult,add ou input
					nItems -= 1
					
					aux = []
					if ops[k-1].split(' ', 1)[0] == "input":
						for j in range (0,nRaizes):
							if j+1 == contaRaiz:
								aux.append((contaRaiz,1))
							else:
								aux.append((j+1,0))
						V[k-1] = P.lagrange_polynomial(aux)
					elif ops[k-1].split(' ', 1)[0] == "mult":
						nAdds = int(ops[k - 1].split(' ', 3)[3])# n de "add" antes desta mult		
						for j in range (0,nRaizes):
							if j+1 == contaRaiz:
								aux.append((contaRaiz,1))
							else:
								aux.append((j+1,0))
						V[k - 1 - nAdds] = P.lagrange_polynomial(aux)
					elif ops[k-1].split(' ', 1)[0] == "add":
						stack.append(int(ops[k - 1].split(' ', 2)[1]))
						stack.append(int(ops[k - 1].split(' ', 2)[2]))
						nItems += 2
									
			###   fim V

			###   W
			aux = []
			indiceDir = int(ops[i].split(' ', 3)[2])
			if ops[indiceDir - 1].split(' ', 1)[0] == "input":
				for j in range (0,nRaizes):
					if j+1 == contaRaiz:
						aux.append((contaRaiz,1))
					else:
						aux.append((j+1,0))
				W[indiceDir - 1] = P.lagrange_polynomial(aux)
			elif ops[indiceDir - 1].split(' ', 1)[0] == "mult":
				nAdds = int(ops[indiceDir - 1].split(' ', 3)[3])# n de "add" antes desta mult		
				for j in range (0,nRaizes):
					if j+1 == contaRaiz:
						aux.append((contaRaiz,1))
					else:
						aux.append((j+1,0))
				W[indiceDir - 1 - nAdds] = P.lagrange_polynomial(aux)
			elif ops[indiceDir - 1].split(' ', 1)[0] == "add":
				stack = []
				nItems = 0

				stack.append(int(ops[indiceDir - 1].split(' ', 2)[1]))
				stack.append(int(ops[indiceDir - 1].split(' ', 2)[2]))
				nItems += 2

				while nItems > 0:
					k = stack[nItems-1] # k (elemento no topo da stack) é o indice do vetor ops que vamos analisar se é mult,add ou input
					nItems -= 1
					
					aux = []
					if ops[k-1].split(' ', 1)[0] == "input":
						for j in range (0,nRaizes):
							if j+1 == contaRaiz:
								aux.append((contaRaiz,1))
							else:
								aux.append((j+1,0))
						W[k-1] = P.lagrange_polynomial(aux)
					elif ops[k-1].split(' ', 1)[0] == "mult":
						nAdds = int(ops[k - 1].split(' ', 3)[3])# n de "add" antes desta mult		
						for j in range (0,nRaizes):
							if j+1 == contaRaiz:
								aux.append((contaRaiz,1))
							else:
								aux.append((j+1,0))
						W[k - 1 - nAdds] = P.lagrange_polynomial(aux)
					elif ops[k-1].split(' ', 1)[0] == "add":
						stack.append(int(ops[k - 1].split(' ', 2)[1]))
						stack.append(int(ops[k - 1].split(' ', 2)[2]))
						nItems += 2
			###   fim W
						
			###   Y
			aux = []
			for j in range (0,nRaizes):
				if j+1 == contaRaiz:
					aux.append((contaRaiz,1))
				else:
					aux.append((j+1,0))

			Y[contaOps] = P.lagrange_polynomial(aux)
			###  fim Y

			contaOps += 1

	#no V,W e Y os indicies que tiverem o valor "#" será adicionado lá o polinomio 0
	#um indice nos vetors de polinomios ter o valor "#" siginica que nesse indice a operaçao nao é esquerda,direita ou resultado de uma mult (raiz)
	for i in range(0,len(V)):
		if V[i] == '#':
			V[i] = P.lagrange_polynomial([(1,0),(2,0)])
		if W[i] == '#':
			W[i] = P.lagrange_polynomial([(1,0),(2,0)])

	return V,W,Y



							#main function

#conjunto de polinomios
V = []
W = []
Y = []
r = 730750818665451621361119245571504901405976559617
Fr = GF(r)
Zn = IntegerModRing(r)
P = PolynomialRing(Fr, 'x') 

condicao = True # condicao do ciclo que vai receber as linhas de texto do ficheiro
outPut = None # se no fim outPut for None então algo correu mal ou entao nao foi encontrada a operacao output

ops = [] # vetor que guarda as operaçoes vindas do ficheiro (operaçoes são: input x,add x y,mult x y)
valores = [] # valores de todas as operacoes
C = [] # valores dos inputs e dos resultados das multiplicacoes, ira ser usado na construcaao do polinomio p
Imid = [] #guarda os indices das operacoes de mult que nao sao inputs nem outputs
nRaizes = 0 #numero de raizes 
contaAdd = 0 #conta o numero de gates "+" antes de uma determinada gate "*" (é importante para calculos futuros)
N = 0 #numero de inputs + numero de outputs 
N_inputs = 0


#vai ler o que vem do ficheiro
try:
	strLida = raw_input()
	while condicao :
		# [0] = "input"            [1] = valor do input
		if strLida.split(' ', 1)[0] == "input":
			N_inputs+=1
			N+=1
			ops.append(strLida)
			# vai buscar o valor do input e passa para inteiro
			valores.append(int(strLida.split(' ', 1)[1]))
			C.append(int(strLida.split(' ', 1)[1]))

			# colocamos '#' para ir preenchendo as posicoes dos vetores para mais tarde poder usar os indices desses vetores e colocar lá o respectivo polinomio 
			V.append('#')
			W.append('#')
			Y.append('#')

			strLida = raw_input()
			
		elif strLida.split(' ', 1)[0] == "add":
			ops.append(strLida)
			# (ex "add 1 2" soma o que esta na posicao 0 com o da posicao 1 do vetor valores e faz o correspontende modulo) 
			contaAdd += 1
			valores.append(Zn(valores[int(strLida.split(' ', 2)[1]) -1] + valores[int(strLida.split(' ', 2)[2]) -1]))
			strLida = raw_input()
			
		elif strLida.split(' ', 1)[0] == "mult":
			Imid.append(len(C))
			#concatena a string lida do ficheiro com o numero de operaçoes "add" antes desta operacao "mult"
			ops.append( strLida + " " + str(contaAdd))
			nRaizes += 1 
			# (ex "mult 1 2" mutiplica o que esta na posicao 0 com o da posicao 1 do vetor valores e faz o correspontende modulo) 
			valores.append(Zn(valores[int(strLida.split(' ', 2)[1]) -1] * valores[int(strLida.split(' ', 2)[2]) -1]))
			C.append(Zn(valores[int(strLida.split(' ', 2)[1]) -1] * valores[int(strLida.split(' ', 2)[2]) -1]))

			V.append('#')
			W.append('#')
			Y.append('#')

			strLida = raw_input()
			
		elif strLida.split(' ', 1)[0] == "output":
			N+=1
			ops.append(strLida)
			#se o output é mult entao vamos tiralo da lista de Imid, lista de intermedios sem ser inputs ou outputs
			if ops[int(strLida.split(' ', 2)[1]) -1].split(' ',1)[0] == "mult":
				nAdds = int(ops[int(strLida.split(' ', 2)[1]) -1].split(' ',3)[3])
				Imid.remove((int(strLida.split(' ', 2)[1]) -1) - nAdds)
			outPut = valores[int(strLida.split(' ', 2)[1]) -1]
			indice_outPut = int(strLida.split(' ', 2)[1]) -1 - nAdds#diz o indice em que esta o output
			condicao = False
		else:
			print "Operacao nao conhecida (operacao recebida do ficheiro nao e input,add, ou mult)"
			condicao = False
except EOFError:
	pass # se der esta exepçao EOF ele vai continuar e ignorar


#contruir a lista de raizes, caso tenha 2 raizes por exemplo esta lista tera os elementos [1,2],servira para contruir o polinomio t
listaRaizes = []
for i in range(0,nRaizes):
	listaRaizes.append(i+1)

t = construirT(listaRaizes)

V,W,Y = construirConjPolinomios(ops,V,W,Y,nRaizes)

resV = 0
resW = 0
resY = 0

for i in range(0,len(V)):
	resV += ZZ(C[i]) * V[i]	
	resW += ZZ(C[i]) * W[i]
	resY += ZZ(C[i]) * Y[i]

p = resV * resW - resY

# p%t se der zero entao t divide p
print p % t

#print "p = " + str(p)
#print "t = " + str(t)

h = p / t

#print "h = " + str(h)

p = 8780710799663312522437781984754049815806883199414208211028653399266475630880222957078625179422662221423155858769582317459277713367317481324925129998224791
cof = 12016012264891146079388821366740534204802954401251311822919615131047207289359704531102844802183906537786776

#def. da curva e ponto base:
F = FiniteField ( p )
E=EllipticCurve(F,[1,0])
# a basePoint of order r
g = cof*E.random_point()

#variaveis que serao usadas no pairing
F2=GF(p**2, name='alpha',modulus=ZZ['x']('x^2+1'));
E2 = E.change_ring(F2)

alpha = F2.gen()

EK = [] # evaluation key
VK = [] # verification key

#inicializar variaveis com valores aleatorios
rv = Fr.random_element()
rw = Fr.random_element()
ry = rv * rw
s = Fr.random_element()
alfa_v = Fr.random_element()
alfa_w = Fr.random_element()
alfa_y = Fr.random_element()
beta = Fr.random_element()
omga = Fr.random_element()
gv = ZZ(rv) * g
gw = ZZ(rw) * g
gy = ZZ(ry) * g

#construir EK
construirEK()

#construir VK
construirVK()


							#compute 

Vmid = 0
Wmid = 0
Ymid = 0
for k in Imid:
	Vmid += ZZ(C[k]) * ZZ(V[k](ZZ(s)))
	Wmid += ZZ(C[k]) * ZZ(W[k](ZZ(s)))
	Ymid += ZZ(C[k]) * ZZ(Y[k](ZZ(s)))

#contruir a prova
proof = []
construirProof()



							#verify

g_vio = ZZ(V[0](s)) * gv * ZZ(C[0])
g_wio = ZZ(W[0](s)) * gw * ZZ(C[0])
g_yio = ZZ(Y[0](s)) * gy * ZZ(C[0])

for k in range(1,N_inputs):
	g_vio += ZZ(V[k](s)) * gv * ZZ(C[k])
	g_wio += ZZ(W[k](s)) * gw * ZZ(C[k])
	g_yio += ZZ(Y[k](s)) * gy * ZZ(C[k])

g_vio += ZZ(V[indice_outPut](s)) * gv * ZZ(C[indice_outPut])
g_wio += ZZ(W[indice_outPut](s)) * gw * ZZ(C[indice_outPut])
g_yio += ZZ(Y[indice_outPut](s)) * gy * ZZ(C[indice_outPut])

#ponto 1 do verify
print pairing(g_vio+proof[0],g_wio+proof[1])==pairing(VK[6],proof[3]) * pairing(g_yio+proof[2],g)

#ponto 2 do verify
print pairing(proof[4],g)==pairing(proof[0],VK[1])
print pairing(proof[5],g)==pairing(proof[1],VK[2])
print pairing(proof[6],g)==pairing(proof[2],VK[3])

#ponto 3 do verify
print pairing(proof[7],VK[4])==pairing(proof[0]+proof[1]+proof[2],VK[5])



