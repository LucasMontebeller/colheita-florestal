
//******* PARAMETROS E CONJUNTOS  ***********/
int nL = ...; //n� de lotes
int nT = ...;  //n� de talh�es
int nV = ...;  //n� de ve�culos
int nE = ...;  //n� de empilhadeiras
float TC = ...;  //Tempo de Carregamento
 
range V = 1..nV;    //Conjundo de ve�culos
range E = 1..nE;	//Conjunto de empilhadeiras
range L = 1..nL;	// Conjunto total de lotes
range T = 1..nT;	// Conjunto de talh�es

int qT[a in T] = ...; //quantidade de lotes por talh�o
int LE[a in 0..nT+1, i in L] = ...;  //matriz bin�ria identifica��o se o lote 'i' pertence ao talh�o 'a'  
// note que � criado o talh�o virtual '0' e 'nT+1', para fazer o sequenciamento de talh�es (isso � uma estrat�gia de sequenciamento). 
float Tida[i in L] = ...;   //tempo da f�brica ao talh�o
float Tvolta[i in L] = 1.15*Tida[i];  //tempo do talh�o para a f�brica
float De[a in 0..nT+1,b in 0..nT+1] = ...; //tempo de deslocament
//************ VARIAVEIS *****************/

dvar boolean X[k in V, i in 0..nL+1, j in 0..nL+1];
//X recebe 1 se o ve�culo 'k' atender� o lote 'j' logo ap�s atender o lote 'i': 
dvar boolean XB[k in V, i in L];
//XB recebe 1 se o ve�culo 'k' atender� o lote 'i'
dvar float+ B[k in V, i in L];
//B � o instante em que o ve�culo 'k' chega no lote 'i'
dvar float+ D[k in V, i in L];
//D � o instante que o ve�culo 'k' come�a a ser carregado como lote 'i'
dvar float+ W[k in V, i in L];
//W � o tempo que o ve�culo 'k' ficou no talh�o esperando para ser carregado como lote 'i'

dvar float+ H[i in L];  //instante que o lote 'i' foi atendido

dvar boolean Y[e in E, a in 0..nT+1, b in 0..nT+1];
//Y recebe 1 se a empilhadeira 'e' atende o lote 'b' logo ap�s atender o lote 'a' 
dvar boolean YB[e in E, a in T];
//YB recebe 1 se a empilhadeira 'e' atender� o talh�o 'a'
dvar float+ C[e in E, a in 0..nT+1];
//dvar float P[e in E, a in 0..nT+1];  //momento que a empilhadeira 'e' deixa o talh�o 'a'

// Tempo que o primeiro veiculo começa a ser atendido em 'a'
dvar float+ F[a in T];

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
  	H[i] <= M;  //nesse caso, 'M' � o instante de atendimento do �ltimo lote (+ tempo de carregamento)
  
 //   M <= 18.9;

//************* restri��es para os ve�culos e lotes

//(1) quarante que todos os lotes ser�o atentendidos   
forall (i in L)
	sum(k in V) XB[k,i] == 1;

//(2)se o ve�culo k n�o atende o lote i, ent�o o ve�culos k n�o atender� 
//nenhum lote antes e depois de 'i'
forall(k in V, i in L, j in L: i!=j)
  (XB[k,i] == 0) => ((X[k,i,j] == 0) && (X[k,j,i] == 0));

//(3) se o ve�culo k atende o lote i, ent�o esse ve�culo de atender algum lote 
//antes ou depois de i (mesmo que seja um lote virtual, de in�cializa��o ou 
//finaliza��o (indices 0 e nL+1))   
forall(k in V, i in L)
  (XB[k,i] == 1) => ((sum(j in 1..nL+1:i!=j) X[k,i,j] == 1) || (sum(j in 0..nL:i!=j) X[k,j,i] == 1));
    
//(4) o n� de transi��es � 1 a menos do que o n� de lotes
forall(k in V)
  sum(i in L, j in L:i!=j) X[k,i,j] == sum(i in L) XB[k,i] - 1;  

//(5) cada ve�culo deve iniciar com algum lote (e exatamente 1 lote)
forall(k in V)
  sum(j in 1..nL+1) X[k,0,j] == 1;
  
//(6) //(5) cada ve�culo deve finalizar com algum lote (e exatamente 1 lote)  
forall(k in V)
  sum(i in 0..nL) X[k,i,nL+1] == 1;

//(7)restri��o de continuidade de fluxo no sequenciamento de lotes
forall(k in V, i in L)
  sum(j in 0..nL) X[k,j,i] - sum (j in 1..nL+1) X[k,i,j] == 0;

//(8) Se o ve�culo k inicial com o lote i ent�o o tempo de atendimento desse lote � igual 
// ao tempo de ida, da f�brica ao lote 
forall(k in V, i in L)
  (X[k,0,i] == 1) => B[k,i] == Tida[i];

//(9) Se o ve�culo k atende o lote j ap�s o lote i, ent�o o tempo de atendimento de j (B[k,j])
//deve ser maior ou igual o 'intante que o ve�culo k cehgou no lote i' + 'o tempo que o ve�culo
//k ficou esperando para atende o lote i' + 'tempo de carrecamento' + 'tempo que o ve�culo 
//gastou para voltar para a f�brica' + 'tempo de ida da f�brila at� o lote i'
forall  (k in V, i in L, j in L:i!=j )
  (X[k,i,j] == 1) => (B[k,j] >= B[k,i] + W[k,i] + TC + Tvolta[i] + Tida[j]);

//(10) tempo de atendimento do lote � igual o tempo que o ve�culo chegou para atender 
//aquele lote + o tempo que fiou esperando  
forall(k in V, i in L)
	D[k,i] == B[k,i]  + W[k,i];
	
//(11) se o veiculo nao atende o lote, o tempo que esse veiculo 'atende' o lote deve ser zero	
forall(k in V, i in L)
	(XB[k,i] == 0) => (D[k,i] == 0);

// Restricao pesada
//(12)	se o ve�culo k atende o lote i, ent�o o tempo de atendimento do ve�culo k no lote i
//deve ser igual ao tempo de atendimento do lote i
forall(k in V, i in L)
	(XB[k,i]==1) => (D[k,i] == H[i]);

//(13) se dois lotes pertencem ao mesmo talh�o, ent�o o instante de carregamento dele deve 
// ter, pelo menos o tempo de carregamento. Pois, cada talh�o � atendimento por apenas uma 
// empilhadeira
forall (i in L, j in L, a in T:i!=j && LE[a,i]==1 && LE[a,j]==1)
  (H[i] >= H[j] + TC) || (H[i] <= H[j] - TC);
  
  //************* restri��es para empilhadeiras
//(14)cada talh�o � atendido por apenas uma empilhadeira
forall (a in T)
  sum(e in E) YB[e,a] == 1;

//(15) an�logo a restri��o (2), por�m para empilhadeiras e talh�es
forall(e in E, a in T, b in T:a!=b)
	(YB[e,a] == 0) => (Y[e,a,b] == 0) && (Y[e,b,a] == 0);  

//(16) an�logo a restri��o (3), por�m para empilhadeiras e talh�es   
forall(e in E, a in T)
  (YB[e,a] == 1) => (sum(b in 1..nT+1:a!=b )Y[e,a,b] == 1) || (sum(b in 0..nT:a!=b)Y[e,b,a] == 1);

//(17) an�logo a restri��o (5), por�m para empilhadeiras e talh�es
forall (e in E)
  sum(b in 1..nT+1) Y[e,0,b] == 1;

//(18)  an�logo a restri��o (6), por�m para empilhadeiras e talh�es
forall (e in E)
  sum(a in 0..nT) Y[e,a,nT+1] == 1;

//(19)  an�logo a restri��o (7), por�m para empilhadeiras e talh�es
forall(e in E, a in T)
  sum(b in 0..nT)Y[e,b,a] - sum(b in 1..nT+1)Y[e,a,b] == 0;

//(20)  an�logo a restri��o (9), por�m para empilhadeiras e talh�es
// se a empilhadeira 'e' atende o talh�o 'b' ap�s o talh�o 'a', o tempo que ela chega no talh�o 
// 'b' deve ser maior ou igual o tempo que ela chega no talh�o 'a' + 
// 'todos os tempo de carregamento de lotes desse talh�o' + 'tempo de deslocamento 
// de 'a' para 'b'
forall(e in E, a in T, b in T:a!=b)
  (Y[e,a,b]==1) => (C[e,b] >= F[a] + TC + De[a,b]);

// Comentário: C na verdade é o instante que a empilhadeira 'e' CHEGA no talhão 'a'. 
// Ainda assim, é necessário incluir o tempo de chegada do primeiro veiculo neste talhao, pois ela nao atende ele no instante zero.
forall(a in T)
  F[a] == min(i in L: LE[a, i] == 1) H[i];
  
// Para melhorar a performance, podemos eliminar a necessidade da variável F[a], igualando essa restrição com a anterior.
forall(e in E, b in T)
  (Y[e, 0, b] == 1) => (C[e, b] == F[b]);

// Restricao Mais Pesada
//(21) se a empilhadeira 'e' atende o talh�o 'b' ap�s o 'a' e o lote i pertence a 'a', ent�o
// o instante de atendimento do lote i deve ser maior do que o tempo de chegada dessa 
// empilhadeira no lote 'a' e menos do que a chegada em 'b' menos o deslocamento de 'a' para 'b' 
forall(e in E, a in 0..nT+1, b in 0..nT+1, i in L:a!=b && LE[a,i]==1 ) //&& LE[b,j]==1)
  (Y[e,a,b]==1) => ((H[i] >= C[e,a]) && (H[i] <= C[e,b] - De[a,b]));
};

// Restricao adicional corrigida
subject to
{
  // se a empilhadeira 'e' não atende o talhão a, o tempo que ela chega no talhão 'a' deve ser zero
  forall(e in E, a in T)
    (YB[e,a] == 0) => (C[e,a] == 0);
}


// Pos processamento
execute {
    // Calcule o gap da solução
    var gap = 100 * (cplex.getMIPRelativeGap());
    
    // Abra o arquivo de saída para escrita
    var file = new IloOplOutputFile("resultado.txt");

    // Salve o valor objetivo e o gap no arquivo de texto
    file.writeln("Objetivo: ", cplex.getObjValue());
    file.writeln("Gap: ", gap);

    file.close();
}

// OBS: Relaxando restr(12) e restr(21) o modelo fica muito mais rapido. Propor heuristica.

/* Perguntas */
// Sera que e possivel fazer um pre-processamento de dados (heuristica)?
// Variavel nao utilizada --> faz sentido eliminar?
