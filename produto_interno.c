int produto(int v[],int a[]){
	int i;
	int soma;
	i = 0;
	soma = 0;
	while(i<3){
		soma = soma + (v[i]*a[i]);
		i = i+1;
	}
	return soma;
}
void main(void){
  int produtoi;
  int cont;
  int a;
  int vetor1[3];
  int vetor2[3];
  cont = 0;
  a = 1;
  while(cont < 3){
	vetor1[cont] = a;
	vetor2[cont] = a;
	cont = cont + 1;
	a = a + 1;
  }
  produtoi = produto(vetor1,vetor2);
}