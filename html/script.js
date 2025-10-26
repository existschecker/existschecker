// infoPanel 要素を一度だけ取得
const infoContent = document.getElementById('infoPanel');
const allHeaders = Array.from(document.querySelectorAll('.block-header'));
let selectedIndex = 0;
const toggleViewBtn = document.getElementById('toggleView');
let currentView = 'syntax';

function highlightBlock(blockElement) {
  // まず既存の selectedblock を解除
  document.querySelectorAll('.block-header.selectedblock').forEach(el => {
    el.classList.remove('selectedblock');
  });

  // blockElement 内のすべての .block-header に追加
  blockElement.querySelectorAll('.block-header').forEach(el => {
    el.classList.add('selectedblock');
  });
}

// 選択状態を更新する関数
function selectHeader(index) {
  const header = allHeaders[index];
  if (!header) return;
  // 選択クラスを更新
  allHeaders.forEach(h => h.classList.remove('selected'));
  header.classList.add('selected');
  selectedIndex = index;
  // ブロック全体をハイライト
  const block = header.closest('.block');  // 選択行が属するブロックを取得
  if (block) highlightBlock(block);
  return header;
}

// infoPanel を更新する関数
function updateInfoPanel(header) {
  let context_vars_label;
  let context_formulas_label;
  let premises_label;
  let conclusions_label;
  let local_vars_label;
  let local_premise_label;
  let local_conclusion_label;

  if (currentView == "syntax") {
    context_vars_label = "context_vars"
    context_formulas_label = "context_formulas"
    premises_label = "premises"
    conclusions_label = "conclusions"
    local_vars_label = "local_vars"
    local_premise_label = "local_premise"
    local_conclusion_label = "local_conclusion"
  } else {
    context_vars_label = "現在使える変数"
    context_formulas_label = "現在使える論理式"
    premises_label = "この文の前提"
    conclusions_label = "この文の結論"
    local_vars_label = "この文のブロック内に追加する変数"
    local_premise_label = "この文のブロック内に追加する前提"
    local_conclusion_label = "この文のブロック内で導く結論"
  }

  const context_vars = header.nextElementSibling;
  const context_formulas = context_vars.nextElementSibling;
  const premises = context_formulas.nextElementSibling;
  const conclusions = premises.nextElementSibling;
  const local_vars = conclusions.nextElementSibling;
  const local_premise = local_vars.nextElementSibling;
  const local_conclusion = local_premise.nextElementSibling;
  infoContent.innerHTML = `
    ${context_vars_label}: ${context_vars.innerHTML}<br>
    ${context_formulas_label}: ${context_formulas.innerHTML}<br>
    ${premises_label}: ${premises.innerHTML}<br>
    ${conclusions_label}: ${conclusions.innerHTML}<br>
    ${local_vars_label}: ${local_vars.innerHTML}<br>
    ${local_premise_label}: ${local_premise.innerHTML}<br>
    ${local_conclusion_label}: ${local_conclusion.innerHTML}
  `;
}

// 必要ならスクロールする関数
function scrollToHeader(header, ctrl) {
  const proofContainer = document.querySelector('.proof');
  const elRect = header.getBoundingClientRect();
  const contRect = proofContainer.getBoundingClientRect();

  if (elRect.top < contRect.top || elRect.bottom > contRect.bottom) {
    header.scrollIntoView({
      behavior: 'smooth',
      block: ctrl ? 'start' : 'center'
    });
  }
}

let isScrolling = false;

function scrollIfNeeded(element, container, ctrl) {
  if (isScrolling) return;

  const elRect = element.getBoundingClientRect();
  const contRect = container.getBoundingClientRect();

  // element が container の表示範囲内に完全に収まっているか
  if (elRect.top < contRect.top || elRect.bottom > contRect.bottom) {
    isScrolling = true;
    element.scrollIntoView({
      behavior: 'smooth',
      block: ctrl ? 'start' : 'center'  // Ctrlなら一番上、それ以外は中央
    });
    setTimeout(() => isScrolling = false, 500); // アニメーション時間に合わせる
  }
}

// 初期選択
if (allHeaders.length > 0) {
  const header = selectHeader(0);
  updateInfoPanel(header);
}

document.addEventListener('click', (e) => {
  if (e.target.matches('.toggle')) {
    const btn = e.target;
    const header = btn.closest('.block-header');
    if (!header) return;
    const content = header.nextElementSibling;
    if (!content || !content.classList.contains('block-content')) return;
    content.classList.toggle('collapsed');
    btn.textContent = content.classList.contains('collapsed') ? '▶' : '▼';
  }
  const header = e.target.closest('.block-header');
  if (header) {
    const index = allHeaders.indexOf(header);
    const h = selectHeader(index);
    updateInfoPanel(h);
  }
});

let keyLocked = false;
document.addEventListener('keydown', (e) => {
  if (e.key !== 'ArrowDown' && e.key !== 'ArrowUp') return;
  e.preventDefault(); // スクロールを止める

  if (keyLocked) return;
  keyLocked = true;
  setTimeout(() => keyLocked = false, 50); // 50ms後に再度処理可能に

  if (allHeaders.length === 0) return;

  let targetIndex = selectedIndex;

  if (e.ctrlKey) {
    if (e.key === 'ArrowUp') {
      // 親をたどってトップノードを見つける
      let block = allHeaders[selectedIndex].closest('.block');
      while (block.parentElement.closest('.block')) {
        block = block.parentElement.closest('.block');
      }
      const topHeader = block.querySelector('.block-header');
      if (allHeaders[selectedIndex] === topHeader) {
        // すでにトップノードなら、1つ前のトップノードへ
        let prevBlock = block.previousElementSibling;
        while (prevBlock && !prevBlock.querySelector('.block-header')) {
          prevBlock = prevBlock.previousElementSibling;
        }
        if (prevBlock) {
          targetIndex = allHeaders.indexOf(prevBlock.querySelector('.block-header'));
        } else {
          targetIndex = selectedIndex; // 最初のトップノードなら移動なし
        }
      } else {
        // 親をたどってトップノードに移動
        targetIndex = allHeaders.indexOf(topHeader);
      }
    } else if (e.key === 'ArrowDown') {
      // 親をたどってトップノードを見つける
      let block = allHeaders[selectedIndex].closest('.block');
      while (block.parentElement.closest('.block')) {
        block = block.parentElement.closest('.block');
      }
      // 次のトップノードがあれば移動
      const nextTopBlock = block.nextElementSibling;
      if (nextTopBlock) {
        targetIndex = allHeaders.indexOf(nextTopBlock.querySelector('.block-header'));
      }
    }
  } else {
    // 通常の上下移動
    if (e.key === 'ArrowDown') {
      targetIndex = Math.min(selectedIndex + 1, allHeaders.length - 1);
    } else if (e.key === 'ArrowUp') {
      targetIndex = Math.max(selectedIndex - 1, 0);
    }
  }

  if (targetIndex === selectedIndex) return; // 移動先が同じなら何もしない

  const h = selectHeader(targetIndex);
  scrollToHeader(h, e.ctrlKey);
  updateInfoPanel(h);
});

document.getElementById('expandAll').addEventListener('click', () => {
  document.querySelectorAll('.block-content').forEach(c => c.classList.remove('collapsed'));
  document.querySelectorAll('.toggle').forEach(b => b.textContent='▼');
});
document.getElementById('collapseAll').addEventListener('click', () => {
  document.querySelectorAll('.block-content').forEach(c => c.classList.add('collapsed'));
  document.querySelectorAll('.toggle').forEach(b => b.textContent='▶');
});

toggleViewBtn.addEventListener('click', () => {
  const proof = document.querySelector('.proof');
  if (currentView === 'syntax') {
    proof.classList.remove('syntax-mode');
    proof.classList.add('jp-mode');
    toggleViewBtn.textContent = 'Syntax';
    currentView = 'jp';
  } else {
    proof.classList.remove('jp-mode');
    proof.classList.add('syntax-mode');
    toggleViewBtn.textContent = '日本語 (Japanese)';
    currentView = 'syntax';
  }
  const header = allHeaders[selectedIndex];
  updateInfoPanel(header);
});
