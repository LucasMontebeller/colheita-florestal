
//******* PARAMETROS E CONJUNTOS  ***********/
int nL = ...; //nº de lotes
int nT = ...;  //nº de talhões
int nV = ...;  //nº de veículos
int nE = ...;  //nº de empilhadeiras
float TC = ...;  //Tempo de Carregamento
 
range V = 1..nV;    //Conjundo de veículos
range E = 1..nE;	//Conjunto de empilhadeiras
range L = 1..nL;	// Conjunto total de lotes
range T = 1..nT;	// Conjunto de talhões

int qT[a in T] = ...; //quantidade de lotes por talhão
int LE[a in 0..nT+1, i in L] = ...;  //matriz binária identificação se o lote 'i' pertence ao talhão 'a'  
// note que é criado o talhão virtual '0' e 'nT+1', para fazer o sequenciamento de talhões (isso é uma estratégia de sequenciamento). 
float Tida[i in L] = ...;   //tempo da fábrica ao talhão
float Tvolta[i in L] = 1.15*Tida[i];  //tempo do talhão para a fábrica
int De[a in 0..nT+1,b in 0..nT+1] = ...; //tempo de deslocamento das empilhadeiras (em os talhões)

//************ VARIAVEIS *****************/

dvar boolean X[k in V, i in 0..nL+1, j in 0..nL+1];
//X recebe 1 se o veículo 'k' atenderá o lote 'j' logo após atender o lote 'i': 
dvar boolean XB[k in V, i in L];
//XB recebe 1 se o veículo 'k' atenderá o lote 'i'
dvar float+ B[k in V, i in L];
//B é o instante em que o veículo 'k' chega no lote 'i'
dvar float+ D[k in V, i in L];
//D é o instante que o veículo 'k' começa a ser carregado como lote 'i'
dvar float+ W[k in V, i in L];
//W é o tempo que o veículo 'k' ficou no talhão esperando para ser carregado como lote 'i'

dvar float+ H[i in L];  //instante que o lote 'i' foi atendido

dvar boolean Y[e in E, a in 0..nT+1, b in 0..nT+1];
//Y recebe 1 se a empilhadeira 'e' atende o lote 'b' logo após atender o lote 'a' 
dvar boolean YB[e in E, a in T];
//YB recebe 1 se a empilhadeira 'e' atenderá o talhão 'a'
dvar float+ C[e in E, a in 0..nT+1];
//dvar float P[e in E, a in 0..nT+1];  //momento que a empilhadeira 'e' deixa o talhão 'a'

dvar float M; 

minimize    
   M;    
//	sum(k in V, i in L) XB[k,i];

subject to {

//forall(e in E, a in T)
//	C[e,a] <= M;

//forall (k in V, i in L)
  //D[k,i] <= M;
  
 forall (i in L)
  	H[i] <= M;  //nesse caso, 'M' é o instante de atendimento do último lote
  
 //   M <= 18.9;

//************* restrições para os veículos e lotes

//(1) quarante que todos os lotes serão atentendidos   
forall (i in L)
	sum(k in V) XB[k,i] == 1;

//(2)se o veículo k não atende o lote i, então o veículos k não atenderá 
//nenhum lote antes e depois de 'i'
forall(k in V, i in L, j in L: i!=j)
  (XB[k,i] == 0) => ((X[k,i,j] == 0) && (X[k,j,i] == 0));

//(3) se o veículo k atende o lote i, então esse veículo de atender algum lote 
//antes ou depois de i (mesmo que seja um lote virtual, de inícialização ou 
//finalização (indices 0 e nL+1))   
forall(k in V, i in L)
  (XB[k,i] == 1) => ((sum(j in 1..nL+1:i!=j) X[k,i,j] == 1) || (sum(j in 0..nL:i!=j) X[k,j,i] == 1));
    
//(4) o nº de transições é 1 a menos do que o nº de lotes
forall(k in V)
  sum(i in L, j in L:i!=j) X[k,i,j] == sum(i in L) XB[k,i] - 1;  

//(5) cada veículo deve iniciar com algum lote (e exatamente 1 lote)
forall(k in V)
  sum(j in 1..nL+1) X[k,0,j] == 1;
  
//(6) //(5) cada veículo deve finalizar com algum lote (e exatamente 1 lote)  
forall(k in V)
  sum(i in 0..nL) X[k,i,nL+1] == 1;

//(7)restrição de continuidade de fluxo no sequenciamento de lotes
forall(k in V, i in L)
  sum(j in 0..nL) X[k,j,i] - sum (j in 1..nL+1) X[k,i,j] == 0;

//(8) Se o veículo k inicial com o lote i então o tempo de atendimento desse lote é igual 
// ao tempo de ida, da fábrica ao lote 
forall(k in V, i in L)
  (X[k,0,i] == 1) => B[k,i] == Tida[i];

//(9) Se o veículo k atende o lote j após o lote i, então o tempo de atendimento de j (B[k,j])
//deve ser maior ou igual o 'intante que o veículo k cehgou no lote i' + 'o tempo que o veículo
//k ficou esperando para atende o lote i' + 'tempo de carrecamento' + 'tempo que o veículo 
//gastou para voltar para a fábrica' + 'tempo de ida da fábrila até o lote i'
forall  (k in V, i in L, j in L:i!=j )
  (X[k,i,j] == 1) => (B[k,j] >= B[k,i] + W[k,i] + TC + Tvolta[i] + Tida[j]);

//(10) tempo de atendimento do lote é igual o tempo que o veículo chegou para atender 
//aquele lote + o tempo que fiou esperando  
forall(k in V, i in L)
	D[k,i] == B[k,i]  + W[k,i];
	
//(11) se o veículo não atendo o lote, o tempo que esse veículo 'atende' o lote deve ser zero	
forall(k in V, i in L)
	(XB[k,i]==0) => (D[k,i] == 0);

//(12)	se o veículo k atende o lote i, então o tempo de atendimento do veículo k no lote i
//deve ser igual ao tempo de atendimento do lote i
forall(k in V, i in L)
	(XB[k,i]==1) => (D[k,i] == H[i]);

//(13) se dois lotes pertencem ao mesmo talhão, então o instante de carregamento dele deve 
// ter, pelo menos o tempo de carregamento. Pois, cada talhão é atendimento por apenas uma 
// empilhadeira
forall (i in L, j in L, a in T:i!=j && LE[a,i]==1 && LE[a,j]==1)
  (H[i] >= H[j] + TC) || (H[i] <= H[j] - TC);
  
  
  //************* restrições para empilhadeiras
//(14)cada talhão é atendido por apenas uma empilhadeira
forall (a in T)
  sum(e in E) YB[e,a] == 1;

//(15) análogo a restrição (2), porém para empilhadeiras e talhões
forall(e in E, a in T, b in T:a!=b)
	(YB[e,a] == 0) => (Y[e,a,b] == 0) && (Y[e,b,a] == 0);  

//(16) análogo a restrição (3), porém para empilhadeiras e talhões   
forall(e in E, a in T)
  (YB[e,a] == 1) => (sum(b in 1..nT+1:a!=b )Y[e,a,b] == 1) || (sum(b in 0..nT:a!=b)Y[e,b,a] == 1);

//(17) análogo a restrição (5), porém para empilhadeiras e talhões
forall (e in E)
  sum(b in 1..nT+1) Y[e,0,b] == 1;

//(18)  análogo a restrição (6), porém para empilhadeiras e talhões
forall (e in E)
  sum(a in 0..nT) Y[e,a,nT+1] == 1;

//(19)  análogo a restrição (7), porém para empilhadeiras e talhões
forall(e in E, a in T)
  sum(b in 0..nT)Y[e,b,a] - sum(b in 1..nT+1)Y[e,a,b] == 0;

//(20)  análogo a restrição (9), porém para empilhadeiras e talhões
// se a empilhadeira 'e' atende o talhão 'b' após o talhão 'a', o tempo que ela chega no talhão 
// 'b' deve ser maior ou igual o tempo que ela chega no talhão 'a' + 
// 'todos os tempo de carregamento de lotes desse talhão' + 'tempo de deslocamento 
// de 'a' para 'b'
forall(e in E, a in T, b in T:a!=b)
  (Y[e,a,b]==1) => (C[e,b] >= C[e,a] + TC * qT[a] + De[a,b]);
  
//(21) se a empilhadeira 'e' atende o talhão 'b' após o 'a' e o lote i pertence a 'a', então
// o instante de atendimento do lote i deve ser maior do que o tempo de chegada dessa 
// empilhadeira no lote 'a' e menos do que a chegada em 'b' menos o deslocamento de 'a' para 'b'   
forall(e in E, a in 0..nT+1, b in 0..nT+1, i in L:a!=b && LE[a,i]==1 ) //&& LE[b,j]==1)
  (Y[e,a,b]==1) => ((H[i] >= C[e,a]) && (H[i] <= C[e,b] - De[a,b]));


  											
};

