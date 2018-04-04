int produto(int v[],int a[], int i){
	int soma;
	int produtoi;
	if(i<3){
		soma = (v[i]*a[i]);
		i = i+1;
		produtoi = produto(v,a,i);
		soma = soma + produtoi;
		return soma;
	}else{
		return 0;
	}
}
void main(void){
  int produtoi;
  int cont;
  int a;
  int vetor1[3];
  int vetor2[3];
  int i;
  i = 0;
  cont = 0;
  a = 1;
  while(cont < 3){
	vetor1[cont] = a;
	vetor2[cont] = a;
	cont = cont + 1;
	a = a + 1;
  }
  produtoi = produto(vetor1,vetor2,i);
}