// infoPanel 要素を一度だけ取得
const infoContent = document.getElementById('infoPanel');
const allHeaders = Array.from(document.querySelectorAll('.block-header'));
let selectedIndex = 0;

// 選択状態を更新する関数
function selectHeader(index) {
  const header = allHeaders[index];
  if (!header) return;
  // 選択クラスを更新
  allHeaders.forEach(h => h.classList.remove('selected'));
  header.classList.add('selected');
  selectedIndex = index;
  return header;
}

// infoPanel を更新する関数
function updateInfoPanel(header) {
  const context_vars = header.nextElementSibling;
  const context_formulas = context_vars.nextElementSibling;
  const premises = context_formulas.nextElementSibling;
  const conclusions = premises.nextElementSibling;
  const local_vars = conclusions.nextElementSibling;
  const local_premise = local_vars.nextElementSibling;
  const local_conclusion = local_premise.nextElementSibling;
  infoContent.innerHTML = `
    Selected line: ${header.innerHTML}<br>
    ${context_vars.innerHTML}<br>
    ${context_formulas.innerHTML}<br>
    ${premises.innerHTML}<br>
    ${conclusions.innerHTML}<br>
    ${local_vars.innerHTML}<br>
    ${local_premise.innerHTML}<br>
    ${local_conclusion.innerHTML}
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
