//***************** PARAMETROS E CONJUNTOS  *****************//
int nL = ...; 												// n de lotes
int nT = ...;  												// n de talhoes
int nV = ...;  												// n de veiculos
int nE = ...;  												// n de empilhadeiras
float TC = ...;  											// Tempo de Carregamento
 
range V = 1..nV;    										// Conjundo de veiculos
range E = 1..nE;											// Conjunto de empilhadeiras
range L = 1..nL;											// Conjunto total de lotes
range T = 1..nT;											// Conjunto de talhoes

int qT[a in T] = ...; 										// quantidade de lotes por talhao
int LE[a in 0..nT+1, i in L] = ...;  						// matriz binaria que indentifica se o lote 'i' pertence ao talhao 'a'  
float Tida[i in L] = ...;   								// tempo da fabrica ao talhao
float Tvolta[i in L] = 1.15*Tida[i];  						// tempo do talhao para a fabrica
float De[a in 0..nT+1,b in 0..nT+1] = ...; 					// tempo de deslocamento entre os talhoes

//***************** VARIAVEIS *****************//
dvar boolean X[k in V, i in 0..nL+1, j in 0..nL+1]; 		// X recebe 1 se o veiculo 'k' atender o lote 'j' logo apos atender o lote 'i'
dvar boolean XB[k in V, i in L];							// XB recebe 1 se o veiculo 'k' atender o lote 'i'
dvar float+ B[k in V, i in L];								// B eh o instante em que o veiculo 'k' chega no lote 'i'
dvar float+ D[k in V, i in L];								// D eh o instante que o veiculo 'k' comeca a ser carregado como lote 'i'
dvar float+ W[k in V, i in L];								// W eh o tempo que o veiculo 'k' ficou no talhao esperando para ser carregado com o lote 'i'

dvar float+ H[i in L];  									// instante que o lote 'i' foi atendido

dvar boolean Y[e in E, a in 0..nT+1, b in 0..nT+1];			// Y recebe 1 se a empilhadeira 'e' atende o talhao 'b' logo apos atender o talhao 'a' 
dvar boolean YB[e in E, a in T];							// YB recebe 1 se a empilhadeira 'e' atende o talhao 'a'
dvar float+ C[e in E, a in 0..nT+1];						// C eh o instante que a empilhadeira 'e' chega no talhao 'a'

dvar float+ M; 												// M representa o instante em que o ultimo lote acaba de ser atendido

//***************** FUNCAO OBJETIVO  *****************//
minimize    
   M;    

//***************** RESTRICOES  *****************//
subject to {

// (0) Estrategia: minimizar o makespan
 forall (i in L)
  	H[i] <= M;
  
// VEICULOS

// (1) Garante que todos os lotes serao atentendidos   
forall (i in L)
	sum(k in V) XB[k,i] == 1;

// (2) Se o veiculo 'k' nao atende o lote 'i', entao nao ira atender nenhum outro antes e depois de 'i'
forall(k in V, i in L, j in L: i!=j)
  (XB[k,i] == 0) => ((X[k,i,j] == 0) && (X[k,j,i] == 0));

// (3) Se o veiculo 'k' atende o lote 'i', entao esse veiculo deve atender algum lote antes ou depois de 'i'
forall(k in V, i in L)
  (XB[k,i] == 1) => ((sum(j in 1..nL+1:i!=j) X[k,i,j] == 1) || (sum(j in 0..nL:i!=j) X[k,j,i] == 1));
    
// (4) O numero de transicoes deve ser 1 a menos do que o numero de lotes (evitar sub-rotas)
forall(k in V)
  sum(i in L, j in L:i!=j) X[k,i,j] == sum(i in L) XB[k,i] - 1;  

// (5) Cada veiculo deve iniciar com algum lote (e exatamente 1 lote)
forall(k in V)
  sum(j in 1..nL+1) X[k,0,j] == 1;
  
// (6) Cada veiculo deve finalizar com algum lote (e exatamente 1 lote)  
forall(k in V)
  sum(i in 0..nL) X[k,i,nL+1] == 1;

// (7) Restricao de continuidade de fluxo no sequenciamento de lotes
forall(k in V, i in L)
  sum(j in 0..nL) X[k,j,i] - sum (j in 1..nL+1) X[k,i,j] == 0;

// (8) Se o veiculo 'k' inicia com o lote i entao o tempo de atendimento desse lote eh igual ao tempo de ida, da fabrica ao lote 
forall(k in V, i in L)
  (X[k,0,i] == 1) => B[k,i] == Tida[i];

// (9) Restricao que garante uma sequência valida de chegada dos veiculos
forall  (k in V, i in L, j in L:i!=j )
  (X[k,i,j] == 1) => (B[k,j] >= B[k,i] + W[k,i] + TC + Tvolta[i] + Tida[j]);

// (10) O tempo de inicio de atendimento de um veiculo eh o tempo que ele chegou no lote acrescido do tempo de espera neste
forall(k in V, i in L)
	D[k,i] == B[k,i]  + W[k,i];
	
// (11) Se o veiculo nao atende o lote, o tempo que esse veiculo inicia o atendimento do lote deve ser zero	
forall(k in V, i in L)
	(XB[k,i] == 0) => (D[k,i] == 0);

// Restricao pesada
// (12) Vincula as variaveis de decisao que representam o inicio de antedimento
forall(k in V, i in L)
	(XB[k,i]==1) => (D[k,i] == H[i]);

//(13) Se dois lotes pertencem ao mesmo talhao, entao a diferenca no inicio de atendimento entre eles deve ser pelo menos o tempo de carregamento, ja que cada talhao so eh atendido por uma unica empilhadeira.
forall (i in L, j in L, a in T:i!=j && LE[a,i]==1 && LE[a,j]==1)
  (H[i] >= H[j] + TC) || (H[i] <= H[j] - TC);
  
// EMPILHADEIRAS
// (14) Analogo a restricao (1), mas para empilhadeiras e talhoes
forall (a in T)
  sum(e in E) YB[e,a] == 1;

// (15) Analogo a restricao (2), mas para empilhadeiras e talhoes
forall(e in E, a in T, b in T:a!=b)
	(YB[e,a] == 0) => (Y[e,a,b] == 0) && (Y[e,b,a] == 0);  

// (16) Analogo a restricao (3), mas para empilhadeiras e talhoes  
forall(e in E, a in T)
  (YB[e,a] == 1) => (sum(b in 1..nT+1:a!=b )Y[e,a,b] == 1) || (sum(b in 0..nT:a!=b)Y[e,b,a] == 1);

// (17) Analogo a restricao (5), mas para empilhadeiras e talhoes  
forall (e in E)
  sum(b in 1..nT+1) Y[e,0,b] == 1;

// (18) Analogo a restricao (6), mas para empilhadeiras e talhoes  
forall (e in E)
  sum(a in 0..nT) Y[e,a,nT+1] == 1;

// (19) Analogo a restricao (7), mas para empilhadeiras e talhoes  
forall(e in E, a in T)
  sum(b in 0..nT)Y[e,b,a] - sum(b in 1..nT+1)Y[e,a,b] == 0;

// (20) Essa restricao era analoga a (9), mas foi modificada conforme descrito abaixo

// Restricao original (artigo)
/*
forall(e in E, a in T, b in T:a!=b && a != 0)
  (Y[e,a,b]==1) => (C[e,b] >= C[e,a] + (qT[a] * TC) + De[a,b]);
*/

// Ajustes realizados: 

// TODO: Verificar se essa restricao nao deixa o modelo mais rapido, apesar de não ser mais necessária.
/*
forall(e in E, a in T, b in T:a!=b && a != 0)
  (Y[e,a,b]==1) => (C[e,b] >= C[e,a] + TC + De[a,b]);
*/

// Comentario: Torna-se necessario incluir o tempo de chegada do primeiro veiculo no respectivo talhao, pois a empilhadeira nao pode atende-lo no instante zero.
// Usando '>=' no lugar de '==' para melhorar o tempo de processamento
forall(e in E, b in T: b != 0)
  (Y[e, 0, b] == 1) => (C[e, b] >= min(i in L: LE[b, i] == 1) H[i]);

// Restricao Mais Pesada
// (21) Restricao que conecta os problemas. Foi necessario incluir TC no limite superior para fazer sentido junto a nova restricao anterior.
forall(e in E, a in 0..nT+1, b in 0..nT+1, i in L:a!=b && LE[a,i]==1)
  (Y[e,a,b]==1) => ((H[i] >= C[e,a]) && (H[i] <= C[e,b] - De[a,b] - TC));

// (22) Analogo a restricao (11), mas para empilhadeiras e talhoes 
  forall(e in E, a in T)
    (YB[e,a] == 0) => (C[e,a] == 0);
};


//***************** POS PROCESSAMENTO  *****************//
execute {
    // Calcula o gap da solução
    var gap = 100 * (cplex.getMIPRelativeGap());
    
    // Abre o arquivo de saída para escrita
    var file = new IloOplOutputFile("resultado.txt");

    // Salva o valor objetivo e o gap no arquivo de texto
    file.writeln("Objetivo: ", cplex.getObjValue());
    file.writeln("Gap: ", gap);

    file.close();
}