#include <cstdio>
#include <stdio.h>
#include <stdlib.h>
#include <cstring>
#include <map>
#include <vector>
#include <queue>
#include <algorithm>
using namespace std;
#define INF 0x3f3f3f3f
/*
1�������ķ�,�Է��ս�����ս������ӳ��
2��������ս����FIRST��
3������Ŀ���ıհ�����(��ǰ������)
4����GO����
5��LR(1)������
6���ϲ�LR(1)�������ڵ�ͬ����Ŀ��
7��LALR(1)������
8�����봮����
ע�⣺
1���������ʽ������100��
2��'@'�����
3��'$'�������Ӳ���ʽ$->S���ع��ķ�
4���ս���ͷ��ս���ĸ�����������20
5����Ŀ��������100
*/
struct grammar {
	char vn, s[10];//����ʽvn->s[10]
}g[100];
int g_num;//��¼����ʽ�ĸ���
map<char, int> vn_map;//�Է��ս������ӳ��
map<char, int> vt_map;//���ս������ӳ��
int vn_num, vt_num;//��¼���ս�����ս���ĸ���
char vn[20], vt[20];//�洢���ս�����ս����ֵ
int first[20][20];//fisrt[i][j]������ս��vn[i]��first�������ս��vt[j]
struct project {
	grammar g;//����ʽ
	int k, pre[20];//�ո��λ��k����ǰ������pre
};
vector<project> closure[100];//��Ŀ��
int closure_num;//��Ŀ���ĸ���
struct Edge {
	int u, v;
	int next;
	char ch;
}edge[1000];//��Ŀ��closure[u]������chת��Ϊ��Ŀ��closure[v]
int go[100];//GO����ͷָ��
int edge_num;//ת��������Ŀ
int belong[100];//�ϲ���Ŀ����Ĺ���
int merge_num;//�ϲ�����Ŀ���ĸ���
int lalr1_action[100][20], lalr1_goto[100][20];//LALR(1)�������action��goto��
											   /*
											   �����ķ�G
											   ���������ʽ
											   �����ķ�
											   �Է��ս�����ս������ӳ��
											   */
void read() 
{
	printf("�������ķ�G,'@'�����\n");
	printf("ֱ������'@'�������\n");
	g_num = 0;
	int i, j, len, flag;
	char ch, str[20];
	grammar temp;
	while (gets_s(str,sizeof(str))) 
	{
		if (str[0] == '@') break;
		len = strlen(str);
		flag = 0;
		if (len < 4) flag = 1;
		else if (str[0] < 'A' || str[0] > 'Z' || str[1] != '-' || str[2] != '>') flag = 1;
		else 
		{
			temp.vn = str[0];
			for (i = 3; i < len; i++) 
			{
				if (str[i] == ' ') break;
				temp.s[i - 3] = str[i];
			}
			temp.s[i - 3] = '\0';
			if (i < len) flag = 1;
		}
		if (flag) 
		{
			printf("����ʽ%s�������ķ������Ѻ��ԡ�\n", str);
			continue;
		}
		else 
		{
			g[++g_num] = temp;
		}
	}
	if (g_num == 0) 
	{
		printf("δ�ɹ��������ʽ\n");
		return;
	}
	printf("������ɣ�������%d������ʽ\n", g_num);
	g[0].vn = '$';
	g[0].s[0] = g[1].vn;
	g[0].s[1] = '\0';
	printf("�ع��ķ�:%c->%s\n", g[0].vn, g[0].s);
	for (i = 1; i <= g_num; i++) 
	{
		printf("\t %c->%s\n", g[i].vn, g[i].s);
	}
	vn_num = vt_num = 0;
	if (vt_map['@'] == 0) 
	{
		vt_map['@'] = ++vt_num;
		vt[vt_num] = '@';
	}
	for (i = 0; i <= g_num; i++) 
	{
		ch = g[i].vn;
		if (vn_map[ch] == 0) 
		{
			vn_map[ch] = ++vn_num;
			vn[vn_num] = ch;
		}
		len = strlen(g[i].s);
		for (j = 0; j < len; j++) 
		{
			ch = g[i].s[j];
			if (ch >= 'A' && ch <= 'Z') continue;
			if (vt_map[ch] == 0) {
				vt_map[ch] = ++vt_num;
				vt[vt_num] = ch;
			}
		}
	}
	if (vt_map['#'] == 0)
	{
		vt_map['#'] = ++vt_num;
		vt[vt_num] = '#';
	}
	for (i = 1, printf("���ս��:\n"); i <= vn_num; i++) 
	{
		printf("%c -> %d\n", vn[i], vn_map[vn[i]]);
	}
	for (i = 1, printf("�ս��:\n"); i <= vt_num; i++) 
	{
		printf("%c -> %d\n", vt[i], vt_map[vt[i]]);
	}
	return;
}
/*
��first��
solve_fisrt()������еķ��ս����first��
dfs(char ch)����ս��ch��first��
*/
void dfs(char ch, int acc[], int vis[], int val[]) 
{
	int i, j, k, c = vn_map[ch];
	if (acc[c])
	{
		for (i = 1; i <= vt_num; i++)
			val[i] = first[c][i];
		return;
	}
	int value[20];
	memset(value, 0, sizeof(value));
	for (i = 0; i <= g_num; i++) 
	{
		if (vis[i]) continue;
		vis[i] = 1;
		if (g[i].vn != ch) continue;
		int len = strlen(g[i].s);
		for (j = 0; j < len; j++) 
		{
			char sh = g[i].s[j];
			if (vn_map[sh]) {
				dfs(sh, acc, vis, value);
				for (k = 2; k <= vt_num; k++) 
				{
					if (value[k]) val[k] = 1;
				}
				if (value[1] == 0) break;
			}
			else 
			{
				c = vt_map[sh];
				val[c] = 1;
				break;
			}
		}
		if (j == len) val[1] = 1;
	}
	return;
}
void solve_first()
{
	int acc[20], vis[20], value[20];
	int i, j, k;
	memset(first, 0, sizeof(first));
	memset(acc, 0, sizeof(acc));
	for (i = 1; i <= vn_num; i++) 
	{
		if (acc[i]) continue;
		memset(vis, 0, sizeof(vis));
		memset(value, 0, sizeof(value));
		dfs(vn[i], acc, vis, value);
		for (j = 1; j <= vt_num; j++)
			first[i][j] = value[j];
		acc[i] = 1;
	}
	printf("���first��\n");
	printf("\t");
	for (i = 1; i <= vt_num; i++)
		printf("%c\t", vt[i]);
	printf("\n");
	for (i = 1; i <= vn_num; i++)
	{
		printf("%c\t", vn[i]);
		for (j = 1; j <= vt_num; j++)
			printf("%d\t", first[i][j]);
		printf("\n");
	}
	return;
}
/*
���հ�����/go����
newproject()���һ���µ���Ŀ
solve_closure()����Ŀ���ıհ�
solve_projects()�����е���Ŀ��
*/
int Equal(grammar u, grammar v) 
{
	if (u.vn != v.vn) return 0;
	if (!strcmp(u.s, v.s)) return 1;
	return 0;
}

int Equal(project u, project v) 
{
	if (!Equal(u.g, v.g)) return 0;
	if (u.k != v.k) return 0;
	for (int i = 1; i <= vt_num; i++)
		if (u.pre[i] != v.pre[i]) return 0;
	return 1;
}

int Equal(int x, int y)
{
	int i, j;
	if (closure[x].size() != closure[y].size()) return 0;
	for (i = 0; i < closure[x].size(); i++) 
	{
		project u = closure[x][i];
		for (j = 0; j < closure[y].size(); j++) 
		{
			project v = closure[y][j];
			if (Equal(u, v)) break;
		}
		if (j == closure[y].size()) break;
	}
	if (i == closure[x].size()) return 1;
	return 0;
}

project newproject()
{
	project temp;
	memset(temp.pre, 0, sizeof(temp.pre));
	return temp;
}

int addproject(project temp, int c)
{
	for (int i = 0; i < closure[c].size(); i++)
	{
		project old = closure[c][i];
		if (Equal(old.g, temp.g) && old.k == temp.k) return i;
	}
	return -1;
}

int solve_closure(int c) 
{
	int i, j, k, l;
	for (i = 0; i < closure[c].size(); i++) 
	{
		project old = closure[c][i];
		int len = strlen(old.g.s);
		if (old.k == len) continue;
		char vn = old.g.s[old.k];
		if (vt_map[vn]) break;
		for (j = 0; j <= g_num; j++) 
		{
			if (g[j].vn != vn) continue;
			//�õ��������Ŀtemp
			project temp = newproject();
			temp.g = g[j];
			temp.k = 0;
			//�ų�S->.@�����
			for (k = 0; k < strlen(g[j].s); k++) 
			{
				if (g[j].s[k] == '@') temp.k++;
				else break;
			}
			char ch = old.g.s[old.k + 1];
			if (ch == '\0')
			{
				for (k = 1; k <= vt_num; k++)
					temp.pre[k] = old.pre[k];
			}
			else if (vn_map[ch]) 
			{
				for (k = 1; k <= vt_num; k++)
					temp.pre[k] = first[vn_map[ch]][k];
			}
			else
				temp.pre[vt_map[ch]] = 1;
			//�ж�temp�Ƿ��Ѿ���������Ŀ����
			int flag = addproject(temp, c);
			if (flag == -1) closure[c].push_back(temp);
			else 
			{
				for (k = 1; k <= vt_num; k++)
					if (temp.pre[k]) closure[c][flag].pre[k] = 1;
			}
		}
	}
	//����µ���Ŀ��closure[c]���ж��Ƿ���ֹ�
	for (i = 1; i < c; i++) 
	{
		if (Equal(i, c)) return i;
	}
	return c;
}

void addedge(int u, int v, char ch) 
{//����GO�����ı�
	edge[edge_num].u = u;
	edge[edge_num].v = v;
	edge[edge_num].ch = ch;
	edge[edge_num].next = go[u];
	go[u] = edge_num++;
}

void solve_projects()
{
	project temp = newproject();
	//��ʼ����Ŀ����������g[0],��ǰ����������'#'
	closure_num = 0;
	temp.g = g[0];
	temp.k = 0;
	temp.pre[vt_map['#']] = 1;
	closure[closure_num + 1].clear();
	closure[closure_num + 1].push_back(temp);
	int c = solve_closure(closure_num + 1);
	if (c == closure_num + 1) 
	{
		closure_num++;
	}
	int i, j, k;
	//��GO����
	memset(go, -1, sizeof(go));
	edge_num = 0;
	for (i = 1; i <= closure_num; i++)
	{
		//������Ŀ�����
		printf("��Ŀ��%d����:\n", i-1);
		for (j = 0; j < closure[i].size(); j++)
		{
			project old = closure[i][j];
			printf("\t%c->", old.g.vn);
			for (k = 0; k <= strlen(old.g.s); k++) 
			{
				if (k == old.k) printf(".");
				printf("%c", old.g.s[k]);
			}
			printf("\t");
			for (k = 1; k <= vt_num; k++)
				if (old.pre[k]) printf("%c ", vt[k]);
			printf("\n");
		}
		//��GO����
		int vis[100];
		memset(vis, 0, sizeof(vis));
		for (j = 0; j < closure[i].size(); j++) 
		{
			if (vis[j]) continue;
			project old = closure[i][j];
			int len = strlen(old.g.s);
			if (old.k == len) continue;
			closure[closure_num + 1].clear();
			for (k = j; k < closure[i].size(); k++) 
			{
				project oldd = closure[i][k];
				if (oldd.g.s[oldd.k] == old.g.s[old.k]) 
				{
					vis[k] = 1;
					project temp = oldd;
					temp.k++;
					closure[closure_num + 1].push_back(temp);
				}
			}
			if (closure[closure_num + 1].size() == 0) continue;
			c = solve_closure(closure_num + 1);
			if (c == closure_num + 1) {
				closure_num++;
			}
			addedge(i, c, old.g.s[old.k]);
		}
	}
	return;
}
/*
���LR(1)������
����״̬��1��closure_num
lr1_action�зǸ���i�����i������ʽ������-i����״̬i
lr1_goto�и���-i����״̬i
*/
int findgrammar(grammar temp) 
{
	for (int i = 0; i <= g_num; i++) 
	{
		if (Equal(temp, g[i])) return i;
	}
}

void printLR1() 
{
	int flag = 0;
	int lr1_action[100][20], lr1_goto[100][20];
	memset(lr1_action, INF, sizeof(lr1_action));
	memset(lr1_goto, INF, sizeof(lr1_goto));
	int i, j, k;
	for (i = 1; i <= closure_num; i++)
	{
		for (j = 0; j < closure[i].size(); j++)
		{
			project old = closure[i][j];
			char ch = old.g.s[old.k];
			int c = findgrammar(old.g);
			if (ch == '\0')
			{
				for (k = 1; k <= vt_num; k++)
				{
					if (old.pre[k]) {
						if (lr1_action[i][k] == INF || lr1_action[i][k] == c)
							lr1_action[i][k] = c;
						else flag = 1;
					}
				}
			}
		}
		for (j = go[i]; j != -1; j = edge[j].next)
		{
			int u = edge[j].u, v = edge[j].v;
			char ch = edge[j].ch;
			if (vn_map[ch]) 
			{
				if (lr1_goto[u][vn_map[ch]] == INF || lr1_goto[u][vn_map[ch]] == -v)
					lr1_goto[u][vn_map[ch]] = -v;
				else flag = 1;
			}
			else 
			{
				if (lr1_action[u][vt_map[ch]] == INF || lr1_action[u][vt_map[ch]] == -v)
					lr1_action[u][vt_map[ch]] = -v;
				else flag = 1;
			}
		}
	}
	if (flag)
	{
		printf("���ֳ�ͻ�����ķ�����LR(1)�ķ�\n");
		return;
	}
	printf("LR(1)������\n");
	printf("״̬\t");
	for (i = 1; i <= vt_num; i++)
		printf("%c\t", vt[i]);
	for (i = 1; i <= vn_num; i++)
		printf("%c\t", vn[i]);
	printf("\n");
	for (i = 1; i <= closure_num; i++)
	{
		printf("%d\t", i);
		for (j = 1; j <= vt_num; j++) 
		{
			k = lr1_action[i][j];
			if (k == INF) printf("\t");
			else if (k < 0) printf("S%d\t", -k);
			else printf("r%d\t", k);
		}
		for (j = 1; j <= vn_num; j++)
		{
			k = lr1_goto[i][j];
			if (k == INF) printf("\t");
			else if (k < 0) printf("%d\t", -k);
			else printf("r%d\t", k);
		}
		printf("\n");
	}
	return;
}

/*
�ϲ�ͬ����Ŀ��
*/
int Equalproject(int x, int y) 
{
	if (closure[x].size() != closure[y].size()) return 0;
	int i, j, k;
	for (i = 0; i < closure[x].size(); i++) 
	{
		project u = closure[x][i];
		for (j = 0; j < closure[y].size(); j++) 
		{
			project v = closure[y][j];
			if (u.k == v.k && Equal(u.g, v.g)) break;
		}
		if (j == closure[y].size()) return 0;
	}
	return 1;
}

void project_merge()
{
	int i, j, k;
	merge_num = 0;//num��ʾ�ϲ����״̬�������
	int vis[100];
	memset(vis, 0, sizeof(vis));
	for (i = 1; i <= closure_num; i++) 
	{
		if (vis[i]) continue;
		belong[i] = ++merge_num;
		vis[i] = 1;
		for (j = i + 1; j <= closure_num; j++)
		{
			if (Equalproject(i, j)) 
			{
				belong[j] = merge_num;
				vis[j] = 1;
			}
		}
	}
	printf("��Ŀ���ϲ�:\n");
	for (i = 1; i <= merge_num; i++) 
	{
		printf("����Ŀ��%d������Ŀ��:", i);
		for (j = 1; j <= closure_num; j++)
			if (belong[j] == i) printf("%d ", j);
		printf("\n");
	}
}
/*
����LALR(1)������
*/
void solve_lalr1()
{
	int flag = 0;
	memset(lalr1_action, INF, sizeof(lalr1_action));
	memset(lalr1_goto, INF, sizeof(lalr1_goto));
	int i, j, k;
	for (i = 1; i <= closure_num; i++)
	{
		for (j = 0; j < closure[i].size(); j++) 
		{
			project old = closure[i][j];
			char ch = old.g.s[old.k];
			int c = findgrammar(old.g);
			if (ch == '\0') {
				for (k = 1; k <= vt_num; k++)
				{
					if (old.pre[k]) 
					{
						if (lalr1_action[belong[i]][k] == INF || lalr1_action[belong[i]][k] == c)
							lalr1_action[belong[i]][k] = c;
						else flag = 1;
					}
				}
			}
		}
		for (j = go[i]; j != -1; j = edge[j].next)
		{
			int u = belong[edge[j].u], v = belong[edge[j].v];
			char ch = edge[j].ch;
			if (vn_map[ch])
			{
				if (lalr1_goto[u][vn_map[ch]] == INF || lalr1_goto[u][vn_map[ch]] == -v)
					lalr1_goto[u][vn_map[ch]] = -v;
				else flag = 1;
			}
			else
			{
				if (lalr1_action[u][vt_map[ch]] == INF || lalr1_action[u][vt_map[ch]] == -v)
					lalr1_action[u][vt_map[ch]] = -v;
				else flag = 1;
			}
		}
	}
	if (flag)
	{
		printf("���ֳ�ͻ�����ķ�����LALR(1)�ķ�\n");
		return;
	}
	printf("LALR(1)������\n");
	printf("״̬\t");
	for (i = 1; i <= vt_num; i++)
		printf("%c\t", vt[i]);
	for (i = 1; i <= vn_num; i++)
		printf("%c\t", vn[i]);
	printf("\n");
	for (i = 1; i <= merge_num; i++)
	{
		printf("%d\t", i);
		for (j = 1; j <= vt_num; j++) 
		{
			k = lalr1_action[i][j];
			if (k == INF) printf("\t");
			else if (k < 0) printf("S%d\t", -k);
			else printf("r%d\t", k);
		}
		for (j = 1; j <= vn_num; j++)
		{
			k = lalr1_goto[i][j];
			if (k == INF) printf("\t");
			else if (k < 0) printf("%d\t", -k);
			else printf("r%d\t", k);
		}
		printf("\n");
	}
	return;
}
/*
�����봮����ƥ��
������ʽS->@������Ҫ����ջ�˳��ַ�
*/
void solve_str() 
{
	printf("���������봮��\n");
	char str[100];
	int step = 0, sta[100];
	char sym[100];
	int sta_num = 0, sym_num = 0;
	sta[sta_num++] = 1;
	sym[sym_num++] = '#';
	int i, j, k, len;
	scanf("%s", str);
	len = strlen(str);
	printf("����\t״̬ջ\t����ջ\t���봮\tACTION\tGOTO\t\n");
	k = 0;
	while (k < len) 
	{
		printf("%d\t", ++step);
		for (i = 0; i < sta_num; i++)
			printf("%d", sta[i]);
		printf("\t");
		for (i = 0; i < sym_num; i++)
			printf("%c", sym[i]);
		printf("\t");
		for (i = k; i < len; i++)
			printf("%c", str[i]);
		printf("\t");
		if (sta_num == 0)
		{
			printf("״̬ջΪ�գ�����\n");
			break;
		}
		int x = sta[sta_num - 1];
		int y = vt_map[str[k]];
		int c = lalr1_action[x][y];
		if (c == INF) 
		{
			printf("ACTION����Ϊ��,����\n");
			break;
		}
		if (c < 0) 
		{
			sta[sta_num++] = -c;
			sym[sym_num++] = str[k++];
			printf("S%d\t\t", -c);
		}
		else 
		{
			if (c == 0)
			{
				printf("acc\n");
				break;
			}
			for (i = 0; i < strlen(g[c].s); i++)
			{
				if (g[c].s[i] != '@')
				{
					sym_num--;
					sta_num--;
				}
			}
			if (sym_num < 0 || sta_num < 0)
			{
				printf("��Լʧ��\n");
				break;
			}
			sym[sym_num++] = g[c].vn;
			x = sta[sta_num - 1];
			y = vn_map[g[c].vn];
			if (lalr1_goto[x][y] == INF)
			{
				printf("GO����Ϊ�գ�����\n");
			}
			sta[sta_num++] = -lalr1_goto[x][y];
			printf("r%d\t%d\t", c, -lalr1_goto[x][y]);
		}
		printf("\n");
	}
	return;
}

int main()
{
	freopen("in2.txt", "r", stdin);
	read();//�����ķ�G(S)
	solve_first();//����ս����first��
	solve_projects();//��հ�������go����
	printLR1();//���LR(1)������
	project_merge();//�ϲ�ͬ����Ŀ��
	solve_lalr1();//����LALR(1)������
	solve_str();//���봮����
	return 0;
}
 