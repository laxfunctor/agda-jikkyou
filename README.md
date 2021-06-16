# Agda 実況

## 動画リスト

1. [【Agda実況】1+1=2の証明、足し算の交換法則の証明](https://youtu.be/0DmIaPFlYOE) : [Nat.agda](https://github.com/laxfunctor/agda-jikkyou/blob/85d8454e1b6eaf7d6e59d96b60cd00ba11629063/Nat.agda)
1. [【Agda実況】掛け算の交換法則の証明](https://youtu.be/dZ3266sdjrw) : [Nat.agda](https://github.com/laxfunctor/agda-jikkyou/blob/84c9bf5ae195c492f78e923310aeb029f5965d47/Nat.agda)
1. [【Agda実況】掛け算の分配法則、結合法則の証明](https://t.co/29RymKS8pV) : [Nat.agda](https://github.com/laxfunctor/agda-jikkyou/blob/c9fbe2756b6f39728e4cdba972d329fc2796bbf0/Nat.agda)

## Agdaのインストール

参考： https://agda.readthedocs.io/en/latest/getting-started/installation.html

### Ubuntu 20.04 でのインストール方法

```
$ sudo install emacs zlib1g-dev libncurses5-dev cabal
$ cabal v2-update
$ cabal v2-install Agda
```
もし、以下のようなエラーメッセージが出てきたら、
```
ghc-pkg dump failed: dieVerbatim: user error (cabal: '/usr/bin/ghc-pkg'
exited with an error:
ghc-pkg: /home/i/.cabal/store/ghc-8.6.5/package.db:
getDirectoryContents:openDirStream: does not exist (No such file or directory)
)
```
ディレクトリを以下のようにして作ればよい。
```
$ mkdir -p ~/.cabal/store/ghc-8.6.5/package.db
```

Emacs で agda-mode を使うには
```
(load-file (let ((coding-system-for-read 'utf-8))
           (shell-command-to-string "agda-mode locate")))
```
を `.emacs` などに追加する。
